{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures, RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, TypeOperators #-}
{-# LANGUAGE IncoherentInstances #-}

module Hatafun where
import Prelude hiding ((^^), (^), mempty)
import Data.Set
import Data.Tuple

data Nat =  Z | S Nat

-- Monotone functions
newtype a -+> b = MFun { unMFun :: a -> b }
infixr 7 -+>

type MVar repr (v :: Nat) (s :: Nat) a =
    forall (v' :: Nat) (s' :: Nat).
    (MonoOps repr, PLUS_GE v s' v') =>
    repr v' s' a

type Var repr (v :: Nat) (s :: Nat) a =
    forall (v' :: Nat) (s' :: Nat).
    (MonoOps repr) =>
    repr v' s' a

class MonoOps (repr :: Nat -> Nat -> * -> *) where
    unlift :: repr v s a -> a
    lift :: a -> repr v s a
    
    fix :: (EqType a, FiniteSemiLattice a) => repr v s (a -+> a) -> repr v s a
    
    lam :: (Var repr v s a -> repr v s b) -> repr v s (a -> b)
    mlam :: (MVar repr v s a -> repr ('S v) ('S s) b) -> repr v s (a -+> b)
    app :: repr v s (a -> b) -> repr v 'Z a -> repr v s b
    mapp :: repr v s (a -+> b) -> repr v s a -> repr v s b
    
    merase :: repr v s (a -+> b) -> repr v s (a -> b)

    test :: repr v 'Z Bool -> repr v s a -> repr v s a -> repr v s a
    when :: SemiLattice a => repr v s Bool -> repr v s a -> repr v s a

class SemiLattice a where
    bot :: MonoOps repr => repr v s a
    lub :: Defn (a -+> a -+> a)

class EqType a where
    eq :: Defn (a -> a -> Bool)

class FinType a where
    elements :: [a]

-- not exactly, there are finite semi-lattices that have top
class (FinType a, SemiLattice a) => FiniteSemiLattice a where
    top :: Defn a

powerset :: Ord a => [a] -> [Set a]
powerset [] = [Data.Set.empty]
powerset (x:xs) = [Data.Set.insert x ps | ps <- powerset xs] ++ powerset xs

instance (FinType a, Ord a) => FinType (Set a) where
    elements = powerset elements

instance (FinType a, Ord a) => FiniteSemiLattice (Set a) where
    top = lift $ Data.Set.fromList $ elements

instance SemiLattice Nat where
    bot = lift Z
    lub = mlam $ \a -> mlam $ \b -> lift (mx (unsafeUnlift a) (unsafeUnlift b))
        where mx Z n = n
              mx n Z = n
              mx (S n) (S m) = S $ mx n m

instance SemiLattice Bool where
    bot = ff
    lub = mlam $ \a -> mlam $ \b -> lift $ (unsafeUnlift a) || (unsafeUnlift b)

instance FinType Bool where
    elements = [True, False]

instance FiniteSemiLattice Bool where
    top = tt

-- Ord is required by Set
instance Ord a => SemiLattice (Set a) where
    bot = mempty
    lub = mlam $ \a -> mlam $ \b -> lift $ union (unsafeUnlift a) (unsafeUnlift b)

instance SemiLattice a => SemiLattice (a, a) where
    -- bot = let ubot = unlift (bot :: forall repr v s a. (MonoOps repr) => repr v s a) in lift (unlift bot, unlift bot)
    bot = lift (unlift bot, unlift bot)


newtype Mono (v :: Nat) (s :: Nat) a = Mono { unMono :: a } deriving Show

instance MonoOps Mono where
    unlift = unMono
    lift = Mono
    fix f =
        let fixpoint mf x = let x' = mf x
                            in if unMono $ eq `app` (Mono x) `app` (Mono x') 
                                then x
                                else fixpoint mf x'
        in Mono $ fixpoint (unMFun (unMono f)) (unMono bot)
    lam f = Mono $ \x -> unMono (f (Mono x))
    mlam f = Mono $ MFun (\x ->  unMono (f (Mono x)))
    app f a = Mono $ (unMono f) (unMono a)
    mapp f a = Mono $ (unMFun.unMono $ f) (unMono a)
    merase f = Mono (unMFun.unMono $ f)
    test cond thn els = if unMono cond then thn else els
    when cond res = if unMono cond then res else bot

λ :: MonoOps repr => (Var repr v s a -> repr v s b) -> repr v s (a -> b)
λ = lam
λ' :: MonoOps repr => (MVar repr v s a -> repr ('S v) ('S s) b) -> repr v s (a -+> b)
λ' = mlam
(^) :: MonoOps repr => repr v s (a -> b) -> repr v 'Z a -> repr v s b
(^) = app
(^^) :: MonoOps repr => repr v s (a -+> b) -> repr v s a -> repr v s b
(^^) = mapp

class PLUS_GE (v :: Nat) (s :: Nat) (v' :: Nat)
instance PLUS_GE a b 'Z
instance PLUS_GE a b a
instance (PLUS_GE v s v') => PLUS_GE v ('S s) ('S v')
instance (PLUS_GE v s v') => PLUS_GE ('S v) s ('S v')

-- Hiding scoping information
type Defn a =
    forall repr (v :: Nat) (s :: Nat).
    MonoOps repr =>
    repr v s a

-- Turn unlift into a monomorphic version, so that
-- type checker could infer
unsafeUnlift :: MonoOps repr => repr 'Z 'Z a -> a
unsafeUnlift = unlift 

-- Pair operators
-- These operations could also be defined in a class as an atomic operation
pair :: Defn (a -+> b -+> (a, b))
pair = mlam $ \a -> mlam $ \b -> lift (unsafeUnlift a, unsafeUnlift b)

fst :: Defn ((a, b) -+> a)
fst = mlam $ \p -> lift (Data.Tuple.fst (unsafeUnlift p))

snd :: Defn ((a, b) -+> b)
snd = mlam $ \p -> lift (Data.Tuple.snd (unsafeUnlift p))

-- Bool operators
tt :: Defn Bool
tt = lift True

ff :: Defn Bool
ff = lift False

-- Set operators
set :: (Ord a) => [a] -> Defn (Set a)
set xs = lift (Data.Set.fromList xs)

mbind :: (Ord a, Ord b) => Defn ((a -> Set b) -+> Set a -+> Set b)
mbind = mlam $ \f -> mlam $ \sa -> 
    lift $ unions $ Data.Set.map (unsafeUnlift f) (unsafeUnlift sa)

mempty :: (Ord a) => Defn (Set a)
mempty = lift $ Data.Set.empty

msingleton :: (Ord a) => Defn (a -> Set a)
msingleton = lam $ \x -> lift $ Data.Set.singleton (unlift x)

mmap :: (Ord a, Ord b) => Defn ((a -> b) -> Set a -+> Set b)
mmap = lam $ \f -> mlam $ \x ->
    mbind `mapp` (lam $ \e -> msingleton `app` (f `app` e)) `mapp` x

mfilter :: Ord a => Defn ((a -> Bool) -+> Set a -+> Set a)
-- failed because this is not monotone (mempty can be replaced with anything)
-- our type system finds it!
-- mfilter = mlam $ \f -> mlam $ \x ->
--     mbind `mapp` (lam $ \e ->
--         test (f `app` e) (msingleton `app` e) (mempty)) `mapp` x
mfilter = mlam $ \f -> mlam $ \x ->
    mbind `mapp` (lam $ \e ->
        when (f `app` e) (msingleton `app` e)) `mapp` x

plus :: Defn (Int -+> Int -+> Int)
plus = mlam $ \a -> mlam $ \b -> lift $ (unsafeUnlift a) + (unsafeUnlift b)

(><) :: (Ord a, Ord b) => Defn (Set a -+> Set b -+> Set (a, b))
(><) = mlam $ \a -> mlam $ \b ->
    mbind `mapp` (lam $ \x ->
        mbind `mapp` (lam $ \y ->
            msingleton `app` (pair `mapp` x `mapp` y)) `mapp` b) `mapp` a

comp :: (Ord a, Ord b, Ord c, EqType b) => Defn (Set (a, b) -+> Set (b, c) -+> Set (a, c))
comp = mlam $ \a -> mlam $ \b ->
    mbind `mapp` (lam $ \x ->
        mbind `mapp` (lam $ \y ->
            let xa = Hatafun.fst `mapp` x
                xb = Hatafun.snd `mapp` x
                yb = Hatafun.fst `mapp` y
                yc = Hatafun.snd `mapp` y in
            when (eq `app` xb `app` yb) $
                msingleton `app` (pair `mapp` xa `mapp` yc))
        `mapp` b)
    `mapp`a


-- tests

data Person = Earendil | Elrond | Arwen deriving (Eq, Ord)
instance SemiLattice Person where
    bot = lift Earendil
    lub = mlam $ \a -> mlam $ \b -> lift (max (unsafeUnlift a) (unsafeUnlift b))
instance FiniteSemiLattice Person where
    top = lift Arwen
parent :: Defn (Set (Person, Person))
parent = set [(Earendil, Elrond), (Elrond, Arwen)]
ancestor :: Defn (Set (Person, Person))
ancestor = fix $ mlam $ \x -> lub `mapp` parent `mapp` (comp `mapp` x `mapp` x)