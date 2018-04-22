-- Copyright (c) 2010-2014, David Amos. All rights reserved.

{-# LANGUAGE TypeFamilies, EmptyDataDecls, MultiParamTypeClasses #-}

-- |A module defining classes and example instances of categories, monoidal categories and braided categories
module Math.QuantumAlgebra.TensorCategory where

import Data.List as L

class MCategory c where
    data Ob c :: *
    data Ar c :: *
    id_ :: Ob c -> Ar c
    source, target :: Ar c -> Ob c
    (>>>) :: Ar c -> Ar c -> Ar c
-- Note that the class Category defined in Control.Category is about categories whose objects are Haskell types,
-- whereas we want the objects to be values of a single type.


class (MCategory a, MCategory b) => MFunctor a b where
    fob :: Ob a -> Ob b -- functor on objects
    far :: Ar a -> Ar b -- functor on arrows

-- We could also define tensor functors and braided functors, which are just functors which commute appropriately
-- with tensor and braiding operations


-- Kassel p282
-- The following is actually definition of a _strict_ monoidal category
-- Also called tensor category
class MCategory c => Monoidal c where
    tunit :: Ob c
    tob :: Ob c -> Ob c -> Ob c -- tensor product of objects
    tar :: Ar c -> Ar c -> Ar c -- tensor product of arrows

class Monoidal c => StrictMonoidal c where {}
-- we want to be able to declare some tensor categories as strict

class Monoidal c => WeakMonoidal c where
    assoc :: Ob c -> Ob c -> Ob c -> Ar c -- assoc u v w is an arrow (natural transformation?): (u `tob` v) `tob` w -> u `tob` (v `tob` w)
    lunit :: Ob c -> Ar c                 -- lunit v is an arrow (isomorphism): tunit `tob` v -> v
    runit :: Ob c -> Ar c                 -- runit v is an arrow (isomorphism): v `tob` tunit -> v

{-
instance (Monoidal c, Eq (Ar c), Show (Ar c)) => Num (Ar c) where
    (*) = tar
-}

class Monoidal c => Braided c where
    twist :: Ob c -> Ob c -> Ar c
    -- twist v w is a map from v tensor w to w tensor v
    -- twist must be natural, and satisfy certain commutative diagrams - Kock 161, 169

class Braided c => Symmetric c where {}
-- if twist satisfies twist v w >>> twist w v == id_ (v tensor w), then the category is symmetric


-- SIMPLEX CATEGORIES

-- Kock, Frobenius Algebras ..., p178-9
-- The skeleton of FinOrd (finite ordered sets)
-- The objects are the finite ordinals n == [0..n-1]
-- The arrows are the order-preserving maps
data FinOrd

instance MCategory FinOrd where
    data Ob FinOrd = FinOrdOb Int deriving (Eq,Ord,Show)
    -- FinOrdOb n represents the oriented simplex n == [0..n-1]
    data Ar FinOrd = FinOrdAr Int Int [Int] deriving (Eq,Ord,Show)
    -- FinOrdAr s t fs represents the order-preserving map, zip [0..s-1] fs.
    -- For example FinOrdAr 3 2 [0,0,1] represents the map 0 -> 0, 1 -> 0, 2 -> 1
    id_ (FinOrdOb n) = FinOrdAr n n [0..n-1]
    source (FinOrdAr s _ _) = FinOrdOb s
    target (FinOrdAr _ t _) = FinOrdOb t
    FinOrdAr sf tf fs >>> FinOrdAr sg tg gs | tf == sg = FinOrdAr sf tg [let j = fs !! i in gs !! j | i <- [0..sf-1] ]

instance Monoidal FinOrd where
    tunit = FinOrdOb 0
    tob (FinOrdOb m) (FinOrdOb n) = FinOrdOb (m+n)
    tar (FinOrdAr sf tf fs) (FinOrdAr sg tg gs) = FinOrdAr (sf+sg) (tf+tg) (fs ++ map (+tf) gs)

finOrdAr s t fs | s == length fs && minimum fs >= 0 && maximum fs < t && isOrderPreserving fs
    = FinOrdAr s t fs
    where isOrderPreserving (f1:f2:fs) = f1 <= f2 && isOrderPreserving (f2:fs)
          isOrderPreserving _ = True


-- The skeleton of FinSet
-- The objects are the finite cardinals n == {0..n-1} (with no order)
-- The arrows are the maps
data FinCard

instance MCategory FinCard where
    data Ob FinCard = FinCardOb Int deriving (Eq,Ord,Show)
    -- FinCardOb n represents the unoriented simplex n == {0..n-1}
    data Ar FinCard = FinCardAr Int Int [Int] deriving (Eq,Ord,Show)
    -- FinCardAr s t fs represents the map, zip [0..s-1] fs.
    -- For example FinCardAr 3 2 [0,1,0] represents the map 0 -> 0, 1 -> 1, 2 -> 0
    id_ (FinCardOb n) = FinCardAr n n [0..n-1]
    source (FinCardAr s _ _) = FinCardOb s
    target (FinCardAr _ t _) = FinCardOb t
    FinCardAr sf tf fs >>> FinCardAr sg tg gs | tf == sg = FinCardAr sf tg [let j = fs !! i in gs !! j | i <- [0..sf-1] ]

instance Monoidal FinCard where
    tunit = FinCardOb 0
    tob (FinCardOb m) (FinCardOb n) = FinCardOb (m+n)
    tar (FinCardAr sf tf fs) (FinCardAr sg tg gs) = FinCardAr (sf+sg) (tf+tg) (fs ++ map (+tf) gs)

finCardAr s t fs | s == length fs && minimum fs >= 0 && maximum fs < t -- for finite cardinals, the map doesn't have to be order-preserving
    = FinCardAr s t fs

-- Finite permutations form a subcategory of FinCard
-- having as objects the finite cardinals n == {0..n-1}
-- and as arrows the bijections (== permutations)
finPerm fs | L.sort fs == [0..n-1] = FinCardAr n n fs
    where n = length fs
-- (Note that these are permutations of [0..n-1], rather than [1..n])


-- This is the forgetful functor FinOrd -> FinCard (FinSet)
instance MFunctor FinOrd FinCard where
    fob (FinOrdOb n) = FinCardOb n
    far (FinOrdAr s t fs) = FinCardAr s t fs


-- BRAID CATEGORY

data Braid

instance MCategory Braid where
    data Ob Braid = BraidOb Int deriving (Eq,Ord,Show)
    data Ar Braid = BraidAr Int [Int] deriving (Eq,Ord,Show)
    id_ (BraidOb n) = BraidAr n []
    source (BraidAr n _) = BraidOb n
    target (BraidAr n _) = BraidOb n
    BraidAr m is >>> BraidAr n js | m == n = BraidAr m (cancel (reverse is) js)
        where cancel (x:xs) (y:ys) = if x+y == 0 then cancel xs ys else reverse xs ++ x:y:ys
              cancel xs ys = reverse xs ++ ys

t n 0 = BraidAr n [] -- the identity braid
t n i |  0 < i && i < n = BraidAr n [i]
      | -n < i && i < 0 = BraidAr n [i]
-- The generators of B_n are [t n i | i <- [1..n-1]]

-- The inverses of the braid generators
t' n i | 0 < i && i < n = BraidAr n [-i]

instance Monoidal Braid where
    tunit = BraidOb 0
    tob (BraidOb m) (BraidOb n) = BraidOb (m+n)
    tar (BraidAr m is) (BraidAr n js) = BraidAr (m+n) (is ++ map (+m) js)

instance Braided Braid where
    twist (BraidOb m) (BraidOb n) = BraidAr (m+n) $ concat [[i..i+n-1] | i <- [m,m-1..1]]

-- Note that in FinCard we consider the objects as [0..n-1], whereas in Braid we consider them as [1..n], so that s_i twists [i,i+1]
instance MFunctor Braid FinCard where
    fob (BraidOb n) = FinCardOb n
    far (BraidAr n ss) = foldr (>>>) (id_ (FinCardOb n)) [finPerm ([0..ti-1] ++ [ti+1,ti] ++ [ti+2..n-1]) | si <- ss, let ti = abs si - 1]


-- VECT

data Vect k

instance Num k => MCategory (Vect k) where
    data Ob (Vect k) = VectOb Int deriving (Eq,Ord,Show)
    data Ar (Vect k) = VectAr Int Int [[Int]] deriving (Eq,Ord,Show)
    id_ (VectOb n) = VectAr n n idMx where idMx = [[if i == j then 1 else 0 | j <- [1..n]] | i <- [1..n]]
    source (VectAr m _ _) = VectOb m
    target (VectAr _ n _) = VectOb n
    VectAr r c xss >>> VectAr r' c' yss | c == r' = undefined -- matrix multiplication

-- functor from FinPerm to Vect k


-- 2-COBORDISMS

data Cob2
-- works very similar to Tangle category

instance MCategory Cob2 where
    data Ob Cob2 = O Int deriving (Eq,Ord,Show)
    data Ar Cob2 = Id Int
                 | Unit
                 | Mult
                 | Counit
                 | Comult
                 | Par (Ar Cob2) (Ar Cob2)
                 | Seq (Ar Cob2) (Ar Cob2)
                 deriving (Eq,Ord,Show)
    id_ (O n) = Id n
    source (Id n) = O n
    source Unit = O 0
    source Mult = O 2
    source Counit = O 1
    source Comult = O 1
    source (Par a b) = O (sa + sb) where O sa = source a; O sb = source b
    source (Seq a b) = source a
    target (Id n) = O n
    target Unit = O 1
    target Mult = O 1
    target Counit = O 0
    target Comult = O 2
    target (Par a b) = O (ta + tb) where O ta = target a; O tb = target b
    target (Seq a b) = target b
    a >>> b | target a == source b = Seq a b

instance Monoidal Cob2 where
    tunit = O 0
    tob (O a) (O b) = O (a+b)
    tar a b = Par a b

-- rewrite a Cob2 so that it is a Seq of Pars
-- (this isn't necessarily going to help us towards a normal form - there may not even be one
rewrite (Par (Seq a1 a2) (Seq b1 b2)) =
    Seq (Par idSourceA b1')
        ( (Seq (Par idSourceA b2')
               (Seq (Par a1' idTargetB)
                    (Par a2' idTargetB) ) ) )
    where idSourceA = id_ (source a1)
          idTargetB = id_ (target b2)
          a1' = rewrite a1
          a2' = rewrite a2
          b1' = rewrite b1
          b2' = rewrite b2
rewrite x = x