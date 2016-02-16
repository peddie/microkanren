{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-|
Module      :  Language.MicroKanren
Copyright   :  (c) 2016 Matt Peddie <mpeddie@gmail.com>
License     :  PublicDomain

Maintainer  :  Matt Peddie <mpeddie@gmail.com>
Stability   :  experimental
Portability :  GHC

An implementation of the microKanren language described in <http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf "μKanren: A Minimal Functional Core for Relational Programming">
by Jason Hemann and Daniel Friedman.

-}

module Language.MicroKanren (
  -- * Logic variables
  Term ( Atom, Null, (:::) )
  , atom
  -- * Relational primitives
  , Program
  , fresh
  , (===)
  , conj
  , disj
    -- * Execute queries on relational programs
  , runAll
  , run
  , traceAll
  , trace
    -- ** Format query results
  , pretty
  , prettyTrace
    -- * Pair/list helpers
  , nullo
  , conso
  , appendo
    -- * Tests/example programs
  , consotest
  , appendotest
  , appendotest2
  ) where

import Prelude hiding ( lookup )
import Control.Applicative ( Alternative(..) )
import Control.Monad
import Control.Monad.Logic
import qualified Control.Monad.Trans.State.Strict as S
import Control.Monad.Trans.State.Strict (StateT)
import qualified Data.IntMap.Strict as M
import qualified Data.IntSet as I
import Data.List ( sortBy )
import Data.Ord ( comparing )
import Data.Generics.Uniplate.Data ( transform )

import Data.Data ( Data )
import Data.Typeable ( Typeable )
import GHC.Generics ( Generic )

{- Logic language terms -}

newtype ConstraintVar = CV Int
                      deriving (Eq, Ord, Show, Read, Generic, Data, Typeable)

-- | Logic variables with Scheme pairs and symbols.
data Term
  = Var ConstraintVar  -- ^ Logic variables
  | Atom String  -- ^ Atom values (like scheme symbols)
  | Null  -- ^ Empty list (i.e. @'()@)
  | Term ::: Term  -- ^ Scheme pairs (you can have improper pairs
                    -- just like in Scheme)
  deriving (Eq, Ord, Show, Read, Generic, Data, Typeable)

infixr 4 :::

-- | Create a symbolic value from anything that can be 'Show'n.
atom :: Show a => a -> Term
atom = Atom . show

{- Logic variable implementation -}

type Mapping = (Int, M.IntMap Term)

-- | A MicroKanren program.
newtype Program a =
  Program { runProgram :: StateT Mapping Logic a }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus, MonadLogic)

get :: Program Mapping
get = Program S.get

put :: Mapping -> Program ()
put f = Program $ S.put f

queryMapping :: Mapping
queryMapping = (1, M.empty)

-- | Generate a new query variable.  For more examples of using
-- 'fresh', see the test/examples functions at the end of this module.
--
-- >>> traceAll $ \_ -> fresh >>= \x -> x === Atom "22"
-- [(2,[(1,Atom "22")])]
fresh :: Program Term
fresh = do
  (count, mapping) <- get
  put (count + 1, mapping)
  return . Var . CV $ count

insert :: ConstraintVar -> Term -> Program ()
insert (CV k) v = do
  (count, mapping) <- get
  put (count, M.insert k v mapping)

-- Lookup with variable cycle-detection.
lookupNoLoop :: M.IntMap Term -> Term -> Term
lookupNoLoop mp x = go I.empty x
  where
    go seen (Var (CV v)) =
      if I.member v seen
      then Var (CV v)
      else case M.lookup v mp of
        Nothing -> Var (CV v)
        Just v' -> go (I.insert v seen) v'
    go _ u = u

lookup :: Term -> Program Term
lookup t = do
  mapping <- snd <$> get
  return $ lookupNoLoop mapping t

-- | Unify two logic variables.
(===) :: Term -> Term -> Program ()
x === y = do
  x' <- lookup x
  y' <- lookup y
  un x' y'
  where
    un (Var a)  (Var b)  | a == b = return ()
    un (Atom a) (Atom b) | a == b = return ()
    un Null Null = return ()
    un (a1 ::: a2) (b1 ::: b2) = a1 === b1 >>- \_ -> a2 === b2
    un (Var a) v = insert a v
    un u (Var b) = insert b u
    un _ _ = mzero
infixr 2 ===

-- | Fair conjunction (the "fair" version of '>>=').  See the docs for
-- 'Control.Monad.Logic.Class.MonadLogic' for more information.
infixr 1 `conj`
conj :: Program a -> Program b -> Program b
conj a b = a >>- \_ -> b

-- | Fair disjunction (the "fair" version of 'mplus').  See the docs
-- for 'Control.Monad.Logic.Class.MonadLogic' for more information.
infixr 0 `disj`
disj :: Program a -> Program a -> Program a
disj = interleave

-- | Substitute known values for all occurrences of bound variables.
tidy :: M.IntMap Term -> M.IntMap Term
tidy mp = fmap (transform replaceVars) mp
  where
    replaceVars t@(Var _) = lookupNoLoop mp t
    replaceVars x = x

-- Run a query, passing it the initial logic var 'q' (this is an
-- internal helper)
query :: (Term -> Program ()) -> [Mapping]
query f = observeAll . flip S.execStateT queryMapping . runProgram $ f queryVar
  where
    queryVar = Var (CV 0)

-- | Run a query, outputting the complete set of logic variable
-- bindings for each result
--
-- >>> traceAll $ \_ -> fresh >>= \x -> x === Atom "22"
-- [(2,[(1,Atom "22")])]
traceAll :: (Term -> Program ()) -> [(Int, [(Int, Term)])]
traceAll f =
  map (\(x, y) -> (x, sortBy (comparing fst) . M.toList $ tidy y)) $ query f

-- | Take the sets of logic variable bindings corresponding to the
-- first @n@ results.
--
-- > trace n = take n . traceAll
trace :: Int -> (Term -> Program ()) -> [(Int, [(Int, Term)])]
trace n = take n . traceAll

-- | Run a query, outputting the binding of the query variable for
-- each result.
--
-- >>> runAll $ \q -> fresh >>= \x -> q === x >> x === Atom "22"
-- [Atom "22"]
--
-- The query variable @q@ may not be bound to any real "value" but
-- just to another logic variable (in this case @x@); when this
-- occurs, the output will look someting like in the following
-- example.  In situations like this, you've either forgotten some
-- unifications or you should just count the length of the return list
-- to see how many solutions there are.
--
-- >>> let test q = do { x <- fresh; q === x }
-- >>> runAll test
-- [Var (CV 1)]
runAll :: (Term -> Program ()) -> [Term]
runAll f = map (flip lookupNoLoop (Var (CV 0)) . tidy . snd) $ query f

-- | Take the query variable values corresponding to the first @n@
-- results.
run :: Int -> (Term -> Program ()) -> [Term]
run n = take n . runAll

-- | Result formatting for 'traceAll' and 'trace'
prettyTrace :: (Show a, Show b, Show c, Foldable t) => [(a, t (b, c))] -> IO ()
prettyTrace [] = putStrLn "==== No solutions found. ===="
prettyTrace xs = mapM_ go xs
  where
    go (count, mappings) = do
      putStrLn $ show count ++ " logic vars:"
      mapM_ formatBinding mappings
    formatBinding (k, v) =
      putStrLn $ "\t" ++ show k ++ " --> '" ++ show v ++ "'"

-- | Result formatting for 'runAll' and 'run'
pretty :: [Term] -> IO ()
pretty [] = putStrLn "==== No solutions found. ===="
pretty xs = mapM_ print xs

-- | The relational form of @null@.
nullo :: Term -> Program ()
nullo = (=== Null)

-- | The relational form of @cons@.
conso :: Term -> Term -> Term -> Program ()
conso x xs lst = lst === x ::: xs

-- | The relational form of @append@/@++@.
appendo :: Term -> Term -> Term -> Program ()
appendo l s out = nullcase `disj` conscase
  where
    nullcase = do
      nullo l
      s === out
    conscase = do
      car <- fresh
      cdr <- fresh
      recout <- fresh
      conso car cdr l
      conso car recout out
      appendo cdr s recout

-- |
-- > consotest q = do
-- >   x <- fresh
-- >   y <- fresh
-- >   q === x ::: y
-- >   let lst = Atom "a" ::: Atom "b" ::: Null
-- >   conso x y lst
--
-- >>> pretty $ runAll consotest
-- Atom "a" ::: (Atom "b" ::: Null)
consotest :: Term -> Program ()
consotest q = do
  x <- fresh
  y <- fresh
  q === x ::: y
  let lst = Atom "a" ::: Atom "b" ::: Null
  conso x y lst

-- |
-- > appendotest q = do
-- >   x <- fresh
-- >   y <- fresh
-- >   appendo x y $ Atom "a" ::: Atom "b" ::: Atom "c" ::: Null
-- >   q === x ::: y
--
-- >>> pretty $ runAll appendotest
-- Null ::: (Atom "a" ::: (Atom "b" ::: (Atom "c" ::: Null)))
-- (Var (CV 3) ::: Var (CV 4)) ::: (Atom "b" ::: (Atom "c" ::: Null))
-- (Var (CV 3) ::: Var (CV 4)) ::: (Atom "c" ::: Null)
-- (Var (CV 3) ::: Var (CV 4)) ::: Null
appendotest :: Term -> Program ()
appendotest q = do
  x <- fresh
  y <- fresh
  appendo x y $ Atom "a" ::: Atom "b" ::: Atom "c" ::: Null
  q === x ::: y

-- |
-- > appendotest2 q = do
-- >   x <- fresh
-- >   y <- fresh
-- >   z <- fresh
-- >   q === x ::: y ::: z
-- >   appendo
-- >     (Atom "a" ::: x ::: Null)
-- >     (Atom "c" ::: y ::: Null)
-- >     (Atom "a" ::: Atom "b" ::: z ::: Atom "d" ::: Null)
--
-- >>> pretty $ runAll appendotest2
-- Atom "b" ::: (Atom "d" ::: Atom "c")
appendotest2 :: Term -> Program ()
appendotest2 q = do
  x <- fresh
  y <- fresh
  z <- fresh
  q === x ::: y ::: z
  appendo
    (Atom "a" ::: x ::: Null)
    (Atom "c" ::: y ::: Null)
    (Atom "a" ::: Atom "b" ::: z ::: Atom "d" ::: Null)
