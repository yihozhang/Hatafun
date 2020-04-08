{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures, RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, TypeOperators #-}
{-# LANGUAGE IncoherentInstances, UndecidableInstances #-}

module Hatafun where
import Prelude hiding ((^^), (^), mempty)
import Data.Set
import Data.Tuple

data Nat =  Z | S Nat

-- Monotone functions
newtype a -+> b = MFun { unMFun :: a -> b }
infixr 7 -+>

class MetaSemiLattice a where
    meta_bot :: a
    meta_lub :: a -> a -> a

class SemiLattice a where
    bot :: Defn a
    lub :: MonoOps repr => repr v s a -> repr v s a -> repr v s a

instance MetaSemiLattice a => SemiLattice a where
    bot = lift meta_bot
    lub x y = lift $ meta_lub (unlift x) (unlift y)

-- equality testing is not monotone
class EqType a where
    eq :: MonoOps repr => repr v 'Z a -> repr v 'Z a -> repr v s Bool

instance Eq a => EqType a where
    eq x y = lift $ (unlift x) == (unlift y)

class FinType a where
    elements :: [a]

class (FinType a, SemiLattice a) => FiniteSemiLattice a where
    top :: a

powerset :: Ord a => [a] -> [Set a]
powerset [] = [Data.Set.empty]
powerset (x:xs) = [Data.Set.insert x ps | ps <- powerset xs] ++ powerset xs

instance (FinType a, Ord a) => FinType (Set a) where
    elements = powerset elements

instance FinType a => FinType (a, a) where
    elements = [(x, y) | x <- elements, y <- elements]

instance (FinType a, Ord a, SemiLattice (Set a)) => FiniteSemiLattice (Set a) where
    top = Data.Set.fromList $ elements

instance MetaSemiLattice Nat where
    meta_bot = Z
    meta_lub = mx
        where mx Z n = n
              mx n Z = n
              mx (S n) (S m) = S $ mx n m

instance MetaSemiLattice Bool where
    meta_bot = False
    meta_lub = (||)

instance FinType Bool where
    elements = [True, False]

-- instance FiniteSemiLattice Bool where
--     top = True

-- Ord is required by Set
instance Ord a => MetaSemiLattice (Set a) where
    meta_bot = empty
    meta_lub = union

instance MetaSemiLattice a => MetaSemiLattice (a, a) where
    meta_bot = (meta_bot, meta_bot)
    meta_lub (a, b) (c, d) = (meta_lub a c, meta_lub b d)

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
    fix :: (Eq a, FiniteSemiLattice a) => repr v s (a -+> a) -> repr v s a
    fix' :: (Eq a, MetaSemiLattice a, SemiLattice a) => repr v s a -> repr v s (a -+> a) -> repr v s a
    lam :: (Var repr v s a -> repr v s b) -> repr v s (a -> b)
    mlam :: (MVar repr v s a -> repr ('S v) ('S s) b) -> repr v s (a -+> b)
    app :: repr v s (a -> b) -> repr v 'Z a -> repr v s b
    mapp :: repr v s (a -+> b) -> repr v s a -> repr v s b
    merase :: repr v s (a -+> b) -> repr v s (a -> b)
    test :: repr v 'Z Bool -> repr v s a -> repr v s a -> repr v s a
    when :: SemiLattice a => repr v s Bool -> repr v s a -> repr v s a

newtype Mono (v :: Nat) (s :: Nat) a = Mono { unMono :: a } deriving (Show, Eq)
instance MonoOps Mono where
    unlift = unMono
    lift = Mono
    fix f =
        let fixpoint mf x = let x' = mf x
                            in if unMono $ eq (Mono x) (Mono x') 
                                then x
                                else fixpoint mf x'
        in Mono $ fixpoint (unMFun (unMono f)) (unMono bot)
    fix' v f = 
        let fixpoint mf x = let x' = mf x
                            in if v /= lub v (Mono x') then unMono v
                            else if x == x' then x
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
pair :: MonoOps repr => repr v s a -> repr v s b -> repr v s (a, b)
pair a b = lift (unlift a, unlift b)

fst :: MonoOps repr => repr v s (a, b) -> repr v s a
fst p = lift (Data.Tuple.fst (unlift p))

snd :: MonoOps repr => repr v s (a, b) -> repr v s b
snd p = lift (Data.Tuple.snd (unlift p))

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

msingleton :: (Ord a, MonoOps repr) => repr v 'Z a -> repr v s (Set a)
msingleton x = lift $ Data.Set.singleton (unlift x)

mmap :: (Ord a, Ord b) => Defn ((a -> b) -> Set a -+> Set b)
mmap = lam $ \f -> mlam $ \x ->
    mbind `mapp` (lam $ \e -> msingleton (f `app` e)) `mapp` x

mfilter :: Ord a => Defn ((a -> Bool) -+> Set a -+> Set a)
-- failed because this is not monotone (mempty can be replaced with anything)
-- our type system finds it!
-- mfilter = mlam $ \f -> mlam $ \x ->
--     mbind `mapp` (lam $ \e ->
--         test (f `app` e) (msingleton `app` e) (mempty)) `mapp` x
mfilter = mlam $ \f -> mlam $ \x ->
    mbind `mapp` (lam $ \e ->
        when (f `app` e) (msingleton e)) `mapp` x

plus :: Defn (Int -+> Int -+> Int)
plus = mlam $ \a -> mlam $ \b -> lift $ (unsafeUnlift a) + (unsafeUnlift b)

(><) :: (Ord a, Ord b, MonoOps repr) => repr v s (Set a) -> repr v s (Set b) -> repr v s (Set (a, b))
a >< b = mbind `mapp` (lam $ \x ->
    mbind `mapp` (lam $ \y ->
        msingleton (pair x y)) `mapp` b) `mapp` a

comp :: (Ord a, Ord b, Ord c, Eq b, MonoOps repr) =>
    repr v s (Set (a, b)) -> repr v s (Set (b, c)) -> repr v s (Set (a, c))
comp a b = mbind `mapp` (lam $ \x ->
        mbind `mapp` (lam $ \y ->
            let xa = Hatafun.fst x
                xb = Hatafun.snd x
                yb = Hatafun.fst y
                yc = Hatafun.snd y in
            when (eq xb yb) $
                msingleton (pair xa yc))
        `mapp` b)
    `mapp`a

-- tests

data Person = Earendil | Elrond | Arwen deriving (Eq, Ord, Show)
instance MetaSemiLattice Person where
    meta_bot = Earendil
    meta_lub = max
instance FinType Person where
    elements = [Earendil, Elrond, Arwen]
instance FiniteSemiLattice Person where
    top = Arwen

parent :: Defn (Set (Person, Person))
parent = set [(Earendil, Elrond), (Elrond, Arwen)]
ancestor :: Defn (Set (Person, Person))
ancestor = fix $ mlam $ \x ->
    lub parent (x `comp` x)

persons :: Defn (Set String)
persons = set ["earendil", "elrond", "arwen"]
parent' :: Defn (Set (String, String))
parent' = set [("earendil", "elrond"), ("elrond", "arwen")]
ancestor' :: Defn (Set (String, String))
ancestor' = fix' (persons >< persons) $ mlam $ \x -> lub parent' (x `comp` x)

trans :: (Eq a, Ord a) => Defn (Set a -+> Set (a, a) -+> Set (a, a))
trans = mlam $ \v -> mlam $ \e ->
    fix' (v >< v) $ mlam $ \s -> lub e (s `comp` s)

ancestor'' :: Defn (Set (String, String))
ancestor'' = trans `mapp` persons `mapp` parent'

eval :: Defn a -> a
eval program = unMono program

main = do
    print $ eval ancestor
    print $ eval ancestor'
    print $ eval ancestor''
    -- fromList [(Earendil,Elrond),(Earendil,Arwen),(Elrond,Arwen)]