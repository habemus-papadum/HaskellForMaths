-- Copyright (c) David Amos, 2008-2015. All rights reserved.

-- |Constructions of the finite geometries AG(n,Fq) and PG(n,Fq), their points, lines and flats,
-- together with the incidence graphs between points and lines.
module Math.Combinatorics.FiniteGeometry where

import Prelude hiding ( (*>) )

import Data.List as L
import qualified Data.Set as S

import Math.Common.ListSet (toListSet)
import Math.Core.Utils

import Math.Core.Field
import Math.Algebra.LinearAlgebra -- hiding ( det )

import Math.Combinatorics.Graph
import Math.Combinatorics.GraphAuts -- for use in GHCi
import Math.Algebra.Group.PermutationGroup hiding (elts) -- for use in GHCi
import Math.Algebra.Group.SchreierSims as SS hiding (elts) -- for use in GHCi

-- !! The following two functions previously required (FiniteField a) as context
-- but this has been temporarily removed to enable them to work with Math.Core.Field

-- |ptsAG n fq returns the points of the affine geometry AG(n,Fq), where fq are the elements of Fq
ptsAG :: Int -> [a] -> [[a]]
ptsAG 0 fq = [[]]
ptsAG n fq = [x:xs | x <- fq, xs <- ptsAG (n-1) fq]

-- |ptsPG n fq returns the points of the projective geometry PG(n,Fq), where fq are the elements of Fq
ptsPG :: Num a => Int -> [a] -> [[a]]
ptsPG 0 _ = [[1]]
ptsPG n fq = map (0:) (ptsPG (n-1) fq) ++ map (1:) (ptsAG n fq)


-- "projective normal form"
pnf (0:xs) = 0 : pnf xs
pnf (1:xs) = 1 : xs
pnf (x:xs) = 1 : map (* x') xs where x' = recip x

ispnf (0:xs) = ispnf xs
ispnf (1:xs) = True
ispnf _ = False

-- closure of points in AG(n,Fq)
-- given p1, .., pk, we're looking for all a1 p1 + ... + ak pk, s.t. a1 + ... + ak = 1
-- if m is the matrix with p1, .., pk as rows, and vs are the vectors [a1, .., ak]
-- then this is the same as [v <*>> m | v <- vs] == [m' <<*> v | v <- vs]

-- |Given a list of points in AG(n,Fq), return their closure, the smallest flat containing them
closureAG :: (Num a, Ord a, FinSet a) => [[a]] -> [[a]]
closureAG ps =
    let vs = [ (1 - sum xs) : xs | xs <- ptsAG (k-1) fq ] -- k-vectors over fq whose sum is 1
    in toListSet [m' <<*> v | v <- vs]
    where k = length ps -- the dimension of the flat (assuming ps are independent)
          m' = L.transpose ps
          fq = elts
-- toListSet call sorts the result, and also removes duplicates in case the points weren't independent

{-
closureAG ps =
    let vs = [ (1 - sum xs) : xs | xs <- ptsAG (k-1) fq ] -- k-vectors over fq whose sum is 1
    in toListSet [foldl1 (<+>) $ zipWith (*>) v ps | v <- vs]
    where k = length ps        -- the dimension of the flat
          fq = eltsFq undefined
-}

lineAG [p1,p2] = L.sort [ p1 <+> (c *> dp) | c <- fq ] where
    dp = p2 <-> p1
    fq = elts

-- closure of points in PG(n,Fq)
-- take all linear combinations of the points (ie the subspace generated by the points, considered as points in Fq ^(n+1) )
-- then discard all which aren't in PNF (thus dropping back into PG(n,Fq))

-- |Given a set of points in PG(n,Fq), return their closure, the smallest flat containing them
closurePG :: (Num a, Ord a, FinSet a) => [[a]] -> [[a]]
closurePG ps = toListSet $ filter ispnf $ map (<*>> ps) $ ptsAG k fq where
    k = length ps
    fq = elts
-- toListSet call sorts the result, and also removes duplicates in case the points weren't independent

linePG [p1,p2] = toListSet $ filter ispnf [(a *> p1) <+> (b *> p2) | a <- fq, b <- fq]
    where fq = elts

-- van Lint & Wilson, p325, 332
qtorial n q | n >= 0 = product [(q^i - 1) `div` (q-1) | i <- [1..n]]

-- van Lint & Wilson, p326
qnomial n k q = (n `qtorial` q) `div` ( (k `qtorial` q) * ((n-k) `qtorial` q) )

-- Cameron, p129
numFlatsPG n q k = qnomial (n+1) (k+1) q -- because it's the number of subspaces in AG n+1 

-- Cameron, p137
numFlatsAG n q k = q^(n-k) * qnomial n k q


qtorials q = scanl (*) 1 [(q^i - 1) `div` (q-1) | i <- [1..]]

qnomials q = iterate succ [1] where
    succ xs = L.zipWith3 (\l r c -> l+c*r) (0:xs) (xs++[0]) (iterate (*q) 1)
    -- succ xs = zipWith (+) (0:xs) $ zipWith (*) (xs++[0]) $ iterate (*q) 1 
-- This amounts to saying
-- [n+1,k]_q = [n,k-1]_q + q^k [n,k]_q
-- Cameron, Combinatorics, p126


-- FLATS VIA REDUCED ROW ECHELON FORMS
-- Suggested by Cameron p125

data ZeroOneStar = Zero | One | Star deriving (Eq)

instance Show ZeroOneStar where
    show Zero = "0"
    show One  = "1"
    show Star = "*"

-- reduced row echelon forms
rrefs n k = map (rref 1 1) (combinationsOf k [1..n]) where
    rref r c (x:xs) =
        if c == x
        then zipWith (:) (oneColumn r) (rref (r+1) (c+1) xs)
        else zipWith (:) (starColumn r) (rref r (c+1) (x:xs))
    rref _ c [] = replicate k (replicate (n+1-c) Star)
    oneColumn r = replicate (r-1) Zero ++ One : replicate (k-r) Zero
    starColumn r = replicate (r-1) Star ++ replicate (k+1-r) Zero


-- flatsPG :: (FiniteField a) => Int -> [a] -> Int -> [[[a]]]

-- |@flatsPG n fq k@ returns the k-flats in PG(n,Fq), where fq are the elements of Fq.
-- The returned flats are represented as matrices in reduced row echelon form,
-- the rows of which are the points that generate the flat.
-- The full set of points in the flat can be recovered by calling 'closurePG'
flatsPG :: (Eq a, Num a) => Int -> [a] -> Int -> [[[a]]]
flatsPG n fq k = concatMap substStars $ rrefs (n+1) (k+1) where
    substStars (r:rs) = [r':rs' | r' <- substStars' r, rs' <- substStars rs]
    substStars [] = [[]]
    substStars' (Star:xs) = [x':xs' | x' <- fq, xs' <- substStars' xs]
    substStars' (Zero:xs) = map (0:) $ substStars' xs
    substStars' (One:xs) = map (1:) $ substStars' xs
    substStars' [] = [[]]


-- Flats in AG(n,Fq) are just the flats in PG(n,Fq) which are not "at infinity"
-- flatsAG :: (FiniteField a) => Int -> [a] -> Int -> [[[a]]]

-- |flatsAG n fq k returns the k-flats in AG(n,Fq), where fq are the elements of Fq.
flatsAG :: (Eq a, Num a) => Int -> [a] -> Int -> [[[a]]]
flatsAG n fq k = [map tail (r : map (r <+>) rs) | r:rs <- flatsPG n fq k, head r == 1]
-- The head r == 1 condition is saying that we want points which are in the "finite" part of PG(n,Fq), not points at infinity
-- The reason we add r to each of the rs is to bring them into the "finite" part
-- (If you don't do this, it can lead to incorrect results, for example some of the flats having the same closure)


-- linesPG :: (FiniteField a) => Int -> [a] -> [[[a]]]

-- |The lines (1-flats) in PG(n,fq)
linesPG :: (Eq a, Num a) => Int -> [a] -> [[[a]]]
linesPG n fq = flatsPG n fq 1

-- linesAG :: (FiniteField a) => Int -> [a] -> [[[a]]]

-- |The lines (1-flats) in AG(n,fq)
linesAG :: (Eq a, Num a) => Int -> [a] -> [[[a]]]
linesAG n fq = flatsAG n fq 1


-- almost certainly not as efficient as linesAG, because requires lineAG/closureAG call
-- among all pairs of distinct points, select those which are the first two in the line they generate
linesAG1 n fq = [ [x,y] | [x,y] <- combinationsOf 2 (ptsAG n fq),
                          [x,y] == take 2 (lineAG [x,y]) ]
-- the point of the condition at the end is to avoid listing the same line more than once

-- almost certainly not as efficient as linesAG, because requires lineAG/closureAG call
-- a line in AG(n,fq) is a translation (x) of a line through the origin (y)
linesAG2 n fq = [ [x,z] | x <- ptsAG n fq, y <- ptsPG (n-1) fq,
                          z <- [x <+> y], [x,z] == take 2 (closureAG [x,z]) ]


-- INCIDENCE GRAPH

-- |Incidence graph of PG(n,fq), considered as an incidence structure between points and lines
incidenceGraphPG :: (Num a, Ord a, FinSet a) => Int -> [a] -> Graph (Either [a] [[a]])
incidenceGraphPG n fq = G vs es where
    points = ptsPG n fq
    lines = linesPG n fq
    vs = L.sort $ map Left points ++ map Right lines
    es = L.sort [ [Left x, Right b] | b <- lines, x <- closurePG b]
-- Could also consider incidence structure between points and planes, etc

-- incidenceAuts (incidenceGraphPG n fq) == PGL(n+1,fq) * auts fq
-- For example, incidenceAuts (incidenceGraphPG 2 f4) =
-- PGL(3,f4) * auts f4
-- where PGL(3,f4)/PSL(3,f4) == f4* (multiplicative group of f4),
-- and auts f4 == { 1, x -> x^2 } (the Frobenius aut)
-- The full group is called PGammaL(3,f4)


-- |Incidence graph of AG(n,fq), considered as an incidence structure between points and lines
incidenceGraphAG :: (Num a, Ord a, FinSet a) => Int -> [a] -> Graph (Either [a] [[a]])
incidenceGraphAG n fq = G vs es where
    points = ptsAG n fq
    lines = linesAG n fq
    vs = L.sort $ map Left points ++ map Right lines
    es = L.sort [ [Left x, Right b] | b <- lines, x <- closureAG b]

-- incidenceAuts (incidenceGraphAG n fq) == Aff(n,fq) * auts fq
-- where Aff(n,fq), the affine group, is the semi-direct product GL(n,fq) * (fq^n)+
-- where (fq^n)+ is the additive group of translations
-- Each elt of Aff(n,fq) is of the form x -> ax + b, where a <- GL(n,fq), b <- (fq^n)+

orderGL n q = product [q^n - q^i | i <- [0..n-1] ]
-- for the first row, we can choose any vector except zero, hence q^n-1
-- for the second row, we can choose any vector except a multiple of the first, hence q^n-q
-- etc

orderAff n q = q^n * orderGL n q

orderPGL n q = orderGL n q `div` (q-1)

-- NOTE:
-- AG(n,F2) is degenerate:
-- Every pair of points is a line, so it is the complete graph on 2^n points
-- And as such has aut group S(2^n)


-- Heawood graph = incidence graph of Fano plane
heawood = to1n $ incidenceGraphPG 2 f2