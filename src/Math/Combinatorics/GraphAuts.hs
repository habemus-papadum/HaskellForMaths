-- Copyright (c) David Amos, 2009-2014. All rights reserved.

{-# LANGUAGE NoMonomorphismRestriction, TupleSections, DeriveFunctor #-}

module Math.Combinatorics.GraphAuts (isVertexTransitive, isEdgeTransitive,
                                     isArcTransitive, is2ArcTransitive, is3ArcTransitive, is4ArcTransitive, isnArcTransitive,
                                     isDistanceTransitive,
                                     graphAuts, incidenceAuts, graphAuts7, graphAuts8, incidenceAuts2,
                                     isGraphAut, isIncidenceAut,
                                     graphIsos, incidenceIsos,
                                     isGraphIso, isIncidenceIso) where

import Data.Either (lefts, rights, partitionEithers)
import qualified Data.List as L
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe
import Data.Ord (comparing)
import qualified Data.Foldable as Foldable
import qualified Data.Sequence as Seq

import Math.Common.ListSet
import Math.Core.Utils (combinationsOf, intersectAsc, pairs, picks, (^-))
import Math.Combinatorics.Graph
-- import Math.Combinatorics.StronglyRegularGraph
-- import Math.Combinatorics.Hypergraph -- can't import this, creates circular dependency
import Math.Algebra.Group.PermutationGroup
import Math.Algebra.Group.SchreierSims as SS


-- The code for finding automorphisms - "graphAuts" - follows later on in file


-- TRANSITIVITY PROPERTIES OF GRAPHS

-- |A graph is vertex-transitive if its automorphism group acts transitively on the vertices. Thus, given any two distinct vertices, there is an automorphism mapping one to the other.
isVertexTransitive :: (Ord t) => Graph t -> Bool
isVertexTransitive (G [] []) = True -- null graph is trivially vertex transitive
isVertexTransitive g@(G (v:vs) es) = orbitV auts v == v:vs where
    auts = graphAuts g

-- |A graph is edge-transitive if its automorphism group acts transitively on the edges. Thus, given any two distinct edges, there is an automorphism mapping one to the other.
isEdgeTransitive :: (Ord t) => Graph t -> Bool
isEdgeTransitive (G _ []) = True
isEdgeTransitive g@(G vs (e:es)) = orbitE auts e == e:es where
    auts = graphAuts g

arc ->^ g = map (.^ g) arc
-- unlike edges/blocks, arcs are directed, so the action on them does not sort

-- Godsil & Royle 59-60
-- |A graph is arc-transitive (or flag-transitive) if its automorphism group acts transitively on arcs. (An arc is an ordered pair of adjacent vertices.)
isArcTransitive :: (Ord t) => Graph t -> Bool
isArcTransitive (G _ []) = True -- empty graphs are trivially arc transitive
isArcTransitive g@(G vs es) = orbit (->^) a auts == a:as where
-- isArcTransitive g@(G vs es) = closure [a] [ ->^ h | h <- auts] == a:as where
    a:as = L.sort $ es ++ map reverse es
    auts = graphAuts g

isArcTransitive' g@(G (v:vs) es) =
    orbitP auts v == v:vs && -- isVertexTransitive g
    orbitP stab n == n:ns
    where auts = graphAuts g
          stab = filter (\p -> v .^ p == v) auts -- relies on v being the first base for the SGS returned by graphAuts
          -- stab = dropWhile (\p -> v .^ p /= v) auts -- we know that graphAuts are returned in this order
          n:ns = nbrs g v

-- execution time of both of the above is dominated by the time to calculate the graph auts, so their performance is similar


-- then k n, kb n n, q n, other platonic solids, petersen graph, heawood graph, pappus graph, desargues graph are all arc-transitive


-- find arcs of length l from x using dfs - results returned in order
-- an arc is a sequence of vertices connected by edges, no doubling back, but self-crossings allowed
findArcs g@(G vs es) x l = map reverse $ dfs [ ([x],0) ] where
    dfs ( (z1:z2:zs,l') : nodes)
        | l == l'   = (z1:z2:zs) : dfs nodes
        | otherwise = dfs $ [(w:z1:z2:zs,l'+1) | w <- nbrs g z1, w /= z2] ++ nodes
    dfs ( ([z],l') : nodes)
        | l == l'   = [z] : dfs nodes
        | otherwise = dfs $ [([w,z],l'+1) | w <- nbrs g z] ++ nodes
    dfs [] = []

-- note that a graph with triangles can't be 3-arc transitive, etc, because an aut can't map a self-crossing arc to a non-self-crossing arc

-- |A graph is n-arc-transitive if its automorphism group is transitive on n-arcs. (An n-arc is an ordered sequence (v0,...,vn) of adjacent vertices, with crossings allowed but not doubling back.)
isnArcTransitive :: (Ord t) => Int -> Graph t -> Bool
isnArcTransitive _ (G [] []) = True
isnArcTransitive n g@(G (v:vs) es) =
    orbitP auts v == v:vs && -- isVertexTransitive g
    orbit (->^) a stab == a:as
    -- closure [a] [ ->^ h | h <- stab] == a:as
    where auts = graphAuts g
          stab = filter (\p -> v .^ p == v) auts -- relies on v being the first base for the SGS returned by graphAuts
          -- stab = dropWhile (\p -> v .^ p /= v) auts -- we know that graphAuts are returned in this order
          a:as = findArcs g v n

is2ArcTransitive :: (Ord t) => Graph t -> Bool
is2ArcTransitive g = isnArcTransitive 2 g

is3ArcTransitive :: (Ord t) => Graph t -> Bool
is3ArcTransitive g = isnArcTransitive 3 g

-- The incidence graphs of the projective planes PG(2,Fq) are 4-arc-transitive
is4ArcTransitive :: (Ord t) => Graph t -> Bool
is4ArcTransitive g = isnArcTransitive 4 g

-- Godsil & Royle 66-7
-- |A graph is distance transitive if given any two ordered pairs of vertices (u,u') and (v,v') with d(u,u') == d(v,v'),
-- there is an automorphism of the graph that takes (u,u') to (v,v')
isDistanceTransitive :: (Ord t) => Graph t -> Bool
isDistanceTransitive (G [] []) = True
isDistanceTransitive g@(G (v:vs) es)
    | isConnected g =
        orbitP auts v == v:vs && -- isVertexTransitive g
        length stabOrbits == diameter g + 1 -- the orbits under the stabiliser of v coincide with the distance partition from v
    | otherwise = error "isDistanceTransitive: only implemented for connected graphs"
    where auts = graphAuts g
          stab = filter (\p -> v .^ p == v) auts -- relies on v being the first base for the SGS returned by graphAuts
          -- stab = dropWhile (\p -> v .^ p /= v) auts -- we know that graphAuts are returned in this order
          stabOrbits = let os = orbits stab in os ++ map (:[]) ((v:vs) L.\\ concat os) -- include fixed point orbits


-- GRAPH AUTOMORPHISMS

-- |Is the permutation an automorphism of the graph?
isGraphAut :: Ord t => Graph t -> Permutation t -> Bool
isGraphAut (G vs es) h = all (`S.member` es') [e -^ h | e <- es]
    where es' = S.fromList es
-- this works best on sparse graphs, where p(edge) < 1/2
-- if p(edge) > 1/2, it would be better to test on the complement of the graph

-- |Is the permutation an automorphism of the incidence structure represented by the graph?
-- (Note that an incidence graph colours points as Left, blocks as Right, and a permutation
-- that swaps points and blocks, even if it is an automorphism of the graph, does not represent
-- an automorphism of the incidence structure. Instead, a point-block crossover is called a duality.)
isIncidenceAut :: (Ord p, Ord b) => Graph (Either p b) -> Permutation (Either p b) -> Bool
isIncidenceAut (G vs es) h = all (`S.member` es') [e ->^ h | e <- es]
    -- using ->^ instead of -^ excludes dualities, since each edge is of the form [Left p, Right b]
    where es' = S.fromList es

-- Calculate a map consisting of neighbour lists for each vertex in the graph
-- If a vertex has no neighbours then it is left out of the map
adjLists (G vs es) = adjLists' M.empty es
    where adjLists' nbrs ([u,v]:es) =
              adjLists' (M.insertWith (flip (++)) v [u] $ M.insertWith (flip (++)) u [v] nbrs) es
          adjLists' nbrs [] = nbrs


-- ALTERNATIVE VERSIONS OF GRAPH AUTS
-- (showing how we got to the final version)

data SearchTree a = T Bool a [SearchTree a] deriving (Eq, Ord, Show, Functor)
-- The boolean indicates whether or not this is a terminal / solution node

leftDepth (T _ _ []) = 1
leftDepth (T _ _ (t:ts)) = 1 + leftDepth t

leftWidths (T _ _ []) = []
leftWidths (T _ _ ts@(t:_)) = length ts : leftWidths t

graphAutsEdgeSearchTree (G vs es) = dfs [] vs vs where
    dfs xys (x:xs) yys = T False xys [dfs ((x,y):xys) xs ys | (y,ys) <- picks yys, isCompatible xys (x,y)]
    dfs xys [] [] = T True xys []
    isCompatible xys (x',y') = and [([x,x'] `S.member` es') == (L.sort [y,y'] `S.member` es') | (x,y) <- xys]
    es' = S.fromList es

graphAuts1 = map fromPairs . terminals . graphAutsEdgeSearchTree

terminals (T False _ ts) = concatMap terminals ts
terminals (T True xys _) = [xys]

-- Using Lemma 9.1.1 from Seress p203 to prune the search tree
-- Because auts form a group, it is sufficient to expand only each leftmost branch of the tree in full.
-- For every other branch, it is sufficient to find a single representative, since the other elements
-- can then be obtained by multiplication in the group (using the leftmost elements).
-- In effect, we are finding a transversal generating set.
-- Note however, that this transversal generating set is relative to whatever base order the tree uses,
-- so for clarity, the tree should use natural vertex order.
transversalTerminals (T False _ (t:ts)) = concatMap (take 1 . transversalTerminals) ts ++ transversalTerminals t
-- transversalTerminals (T False _ (t:ts)) = transversalTerminals t ++ concatMap (take 1 . transversalTerminals) ts
transversalTerminals (T True xys _) = [xys]
transversalTerminals _ = []

graphAuts2 = filter (/=1) . map fromPairs . transversalTerminals . graphAutsEdgeSearchTree
-- init because last is identity

isSingleton [_] = True
isSingleton _ = False

intersectCells p1 p2 = concat [ [c1 `intersectAsc` c2 | c2 <- p2] | c1 <- p1]
-- Intersection preserves ordering within cells but not between cells
-- eg the cell [1,2,3,4] could be refined to [2,4],[1,3]


graphAutsDistancePartitionSearchTree g@(G vs es) = dfs [] ([vs],[vs]) where
    dfs xys (srcPart,trgPart)
        | all isSingleton srcPart =
             let xys' = zip (concat srcPart) (concat trgPart)
             in T (isCompatible xys') (xys++xys') []
             -- Since the xys' are distance-compatible with the xys, they are certainly edge-compatible.
             -- However, we do need to check that the xys' are edge-compatible with each other.
        | otherwise = let (x:xs):srcCells = srcPart
                          yys   :trgCells = trgPart
                          srcPart' = intersectCells (xs : srcCells) (dps M.! x)
                      in T False xys -- the L.sort in the following line is so that we traverse vertices in natural order
                         [dfs ((x,y):xys) ((unzip . L.sort) (zip (filter (not . null) srcPart') (filter (not . null) trgPart')))
                         | (y,ys) <- picks yys,
                           let trgPart' = intersectCells (ys : trgCells) (dps M.! y),
                           map length srcPart' == map length trgPart']
    isCompatible xys = and [([x,x'] `S.member` es') == (L.sort [y,y'] `S.member` es') | (x,y) <- xys, (x',y') <- xys, x < x']
    es' = S.fromList es
    dps = M.fromAscList [(v, distancePartitionS vs es' v) | v <- vs]

graphAuts3 = filter (/=1) . map fromPairs . transversalTerminals . graphAutsDistancePartitionSearchTree

-- Whereas transversalTerminals produced a transversal generating set, here we produce a strong generating set.
-- In particular, if we have already found (3 4), and then we find (1 2 3),
-- then there is no need to look for (1 3 ...) or (1 4 ...), since it is clear that such elements exist
-- as products of those we have already found.
strongTerminals = strongTerminals' [] where
    strongTerminals' gs (T False xys ts) =
        case listToMaybe $ reverse $ filter (\(x,y) -> x /= y) xys of -- the first vertex that isn't fixed
        Nothing -> L.foldl' (\hs t -> strongTerminals' hs t) gs ts
        Just (x,y) -> if y `elem` (x .^^ gs)
                      then gs
                      -- Since we're not on the leftmost spine, we can stop as soon as we find one new element
                      else find1New gs ts
                      -- else L.foldl' (\hs t -> if hs /= gs then hs else strongTerminals' hs t) gs ts
    strongTerminals' gs (T True xys []) = fromPairs xys : gs
    find1New gs (t:ts) = let hs = strongTerminals' gs t
                         in if take 1 gs /= take 1 hs -- we know a new element would be placed at the front
                            then hs
                            else find1New gs ts
    find1New gs [] = gs

-- |Given a graph g, @graphAuts g@ returns a strong generating set for the automorphism group of g.
graphAuts :: (Ord a) => Graph a -> [Permutation a]
graphAuts = filter (/=1) . strongTerminals . graphAutsDistancePartitionSearchTree


-- Using colourings (M.Map vertex colour, M.Map colour [vertex]), in place of partitions ([[vertex]])
-- This turns out to be slower than using partitions.
-- Updating the colour partition incrementally seems to be much less efficient than just recalculating it each time
-- (Recalculating each time is O(n), incrementally updating is O(n^2)?)
graphAutsDistanceColouringSearchTree g@(G vs es) = dfs [] unitCol unitCol where
    unitCol = (M.fromList $ map (,[]) vs, M.singleton [] vs) -- "unit colouring"
    dfs xys srcColouring@(srcVmap,srcCmap) trgColouring@(trgVmap,trgCmap)
        -- ( | M.map length srcCmap /= M.map length trgCmap = T False xys [] )
        | all isSingleton (M.elems srcCmap) = -- discrete colouring
             let xys' = zip (concat $ M.elems srcCmap) (concat $ M.elems trgCmap)
             in T (isCompatible xys') (reverse xys'++xys) []
             -- Since the xys' are distance-compatible with the xys, they are certainly edge-compatible.
             -- However, we do need to check that the xys' are edge-compatible with each other.
        | otherwise = let (x,c) = M.findMin srcVmap
                          (xVmap,xCmap) = dcs M.! x
                          ys = trgCmap M.! c
                          srcVmap' = M.delete x (intersectColouring srcVmap xVmap)
                          srcCmap' = colourPartition srcVmap'
                          -- srcCmap' = M.fromAscList [(c1++c2, cell) | (c1,srcCell) <- M.assocs srcCmap, (c2,xCell) <- M.assocs xCmap,
                          --                                            let cell = L.delete x (intersectAsc srcCell xCell),
                          --                                            (not . null) cell]
                      in T False xys
                         [dfs ((x,y):xys) (srcVmap',srcCmap') (trgVmap',trgCmap')
                         | y <- ys,
                           let (yVmap,yCmap) = dcs M.! y,
                           let trgVmap' = M.delete y (intersectColouring trgVmap yVmap),
                           let trgCmap' = colourPartition trgVmap',
                           -- let trgCmap' = M.fromAscList [(c1++c2, cell) | (c1,trgCell) <- M.assocs trgCmap, (c2,yCell) <- M.assocs yCmap,
                           --                                                let cell = L.delete y (intersectAsc trgCell yCell),
                           --                                                (not . null) cell],
                           M.map length srcCmap' == M.map length trgCmap' ]
    isCompatible xys = and [([x,x'] `S.member` es') == (L.sort [y,y'] `S.member` es') | (x,y) <- xys, (x',y') <- xys, x < x']
    es' = S.fromList es
    dcs = M.fromAscList [(v, distanceColouring v) | v <- vs]
    distanceColouring u = let dp = distancePartitionS vs es' u
                              vmap = M.fromList [(v,[c]) | (cell,c) <- zip dp [0..], v <- cell]
                              cmap = M.fromList $ zip (map (:[]) [0..]) dp
                          in (vmap, cmap)

{-
-- If we are going to recalculate the colour partition each time anyway,
-- then we don't need to carry it around, and can simplify the code
graphAutsDistanceColouringSearchTree g@(G vs es) = dfs [] initCol initCol where
    initCol = M.fromList $ map (,[]) vs
    dfs xys srcCol trgCol
        | M.map length srcPart /= M.map length trgPart = T False xys []
        | all isSingleton (M.elems srcPart) =
             let xys' = zip (concat $ M.elems srcPart) (concat $ M.elems trgPart)
             in T (isCompatible xys') (reverse xys'++xys) []
             -- Since the xys' are distance-compatible with the xys, they are certainly edge-compatible.
             -- However, we do need to check that the xys' are edge-compatible with each other.
        | otherwise = let (x,c) = M.findMin srcCol
                          ys = trgPart M.! c
                          srcCol' = M.delete x $ intersectColouring srcCol (dcs M.! x)
                      in T False xys
                         [dfs ((x,y):xys) srcCol' trgCol'
                         | y <- ys,
                           let trgCol' = M.delete y (intersectColouring trgCol (dcs M.! y))]
        where srcPart = colourPartition srcCol
              trgPart = colourPartition trgCol
    isCompatible xys = and [([x,x'] `S.member` es') == (L.sort [y,y'] `S.member` es') | (x,y) <- xys, (x',y') <- xys, x < x']
    es' = S.fromList es
    dcs = M.fromAscList [(v, distanceColouring v) | v <- vs]
    distanceColouring u = M.fromList [(v,[c]) | (cell,c) <- zip (distancePartitionS vs es' u) [0..], v <- cell]
-}
distanceColouring (G vs es) u = M.fromList [(v,[c]) | (cell,c) <- zip (distancePartitionS vs es' u) [0..], v <- cell]
    where es' = S.fromList es

intersectColouring c1 c2 = M.intersectionWith (++) c1 c2

colourPartition c = L.foldr (\(k,v) m -> M.insertWith (++) v [k] m) M.empty (M.assocs c)



-- Based on McKay’s Canonical Graph Labeling Algorithm, by Stephen G. Hartke and A. J. Radcliffe
-- (http://www.math.unl.edu/~aradcliffe1/Papers/Canonical.pdf)

equitableRefinement g@(G vs es) p = equitableRefinement' (S.fromList es) p

equitableRefinement' edgeset partition = go partition where
    go cells = let splits = L.zip (L.inits cells) (L.tails cells)
                   shatterPairs = [(L.zip ci counts,ls,rs) | (ls,ci:rs) <- splits, cj <- cells,
                                                             let counts = map (nbrCount cj) ci, isShatter counts]
               in case shatterPairs of -- by construction, the lexicographic least (i,j) comes first
                  [] -> cells
                  (vcs,ls,rs):_ -> let fragments = shatter vcs 
                                   in go (ls ++ fragments ++ rs)
    isShatter (c:cs) = any (/= c) cs
    shatter vcs = map (map fst) $ L.groupBy (\x y -> snd x == snd y) $ L.sortBy (comparing snd) $ vcs
    -- Memoizing here results in about 10% speed improvement. Not worth it for loss of generality (ie requiring HasTrie instances)
    -- nbrCount = memo2 nbrCount'
    -- How many neighbours in cell does vertex have
    nbrCount cell vertex = length (filter (isEdge vertex) cell)
    isEdge u v = L.sort [u,v] `S.member` edgeset

equitablePartitionSearchTree g@(G vs es) p = dfs [] p where
    dfs bs p = let p' = equitableRefinement' es' p in
               if all isSingleton p'
               then T True (p',bs) []
               else T False (p',bs) [dfs (b:bs) p'' | (b,p'') <- splits [] p']
    -- For now, we just split the first non-singleton cell we find
    splits ls (r:rs) | isSingleton r = splits (r:ls) rs
                     | otherwise = let ls' = reverse ls in [(x, ls' ++ [x]:xs:rs) | (x,xs) <- picks r]
    es' = S.fromList es


{-
-- Using Data.Sequence instead of list for the partitions
-- Makes no difference to speed (in fact slightly slower)
equitableRefinementSeq' edgeset partition = go partition where
    go cells = let splits = Seq.zip (Seq.inits cells) (Seq.tails cells)
                   shatterPairs = [(L.zip ci counts,ls,rs') | (ls,rs) <- Foldable.toList splits, (not . Seq.null) rs, let ci Seq.:< rs' = Seq.viewl rs,
                                                              cj <- Foldable.toList cells,
                                                              let counts = map (nbrCount cj) ci, isShatter counts]
               in case shatterPairs of -- by construction, the lexicographic least (i,j) comes first
                  [] -> cells
                  (vcs,ls,rs):_ -> let fragments = Seq.fromList (shatter vcs) 
                                   in go (ls Seq.>< fragments Seq.>< rs)
    isShatter (c:cs) = any (/= c) cs
    shatter vcs = map (map fst) $ L.groupBy (\x y -> snd x == snd y) $ L.sortBy (comparing snd) $ vcs
    -- How many neighbours in cell does vertex have
    nbrCount cell vertex = length (filter (isEdge vertex) cell)
    isEdge u v = L.sort [u,v] `S.member` edgeset

equitablePartitionSeqSearchTree g@(G vs es) p = dfs [] (Seq.fromList p) where
    dfs bs p = let p' = equitableRefinementSeq' es' p in
               if Foldable.all isSingleton p'
               then T True (Foldable.toList p',bs) []
               else T False (Foldable.toList p',bs) [dfs (b:bs) p'' | (b,p'') <- splits p']
    -- For now, we just split the first non-singleton cell we find
    splits cells = case Seq.findIndexL (not . isSingleton) cells of
                   Just i -> let (ls,rs) = Seq.splitAt i cells
                                 r Seq.:< rs' = Seq.viewl rs
                             in [(x, ls Seq.>< ([x] Seq.<| xs Seq.<| rs')) | (x,xs) <- picks r]
                   Nothing -> error "Not possible, as we know there are non-singleton cells"
    es' = S.fromList es
-}

-- In this version, whenever we have an equitable partition, we separate out all the singleton cells and put them to one side.
-- (Since the partition is equitable, singleton cells have already done any work they are going to do in shattering other cells,
-- so they will no longer play any part.)
-- This seems to result in about 20% speedup.
equitablePartitionSearchTree2 g@(G vs es) p = dfs [] ([],p) where
    dfs bs (ss,cs) = let (ss',cs') = L.partition isSingleton $ equitableRefinement' es' cs
                         ss'' = ss++ss'
                     in case cs' of
                        [] -> T True (ss'',bs) []
                        -- We just split the first non-singleton cell
                        -- c:cs'' -> T False (ss''++cs',bs) [dfs (x:bs) (ss'',[x]:xs:cs'') | (x,xs) <- picks c]
                        c:cs'' -> T False (cs'++ss'',bs) [dfs (x:bs) (ss'',[x]:xs:cs'') | (x,xs) <- picks c]
    es' = S.fromList es
-- TODO: On the first level, we can use a stronger partitioning function (eg distance partitions, + see nauty manual, vertex invariants)

equitableDistancePartitionSearchTree g@(G vs es) p = dfs [] p where
    dfs bs p = let p' = equitableRefinement' es' p in
               if all isSingleton p'
               then T True (p',bs) []
               else T False (p',bs) [dfs (b:bs) p'' | (b,p'') <- splits [] p']
    -- For now, we just split the first non-singleton cell we find
    splits ls (r:rs) | isSingleton r = splits (r:ls) rs
                     | otherwise = [(x, p'') | let ls' = reverse ls,
                                               (x,xs) <- picks r,
                                               let p' = ls' ++ [x]:xs:rs,
                                               let p'' = filter (not . null) (intersectCells p' (dps M.! x))]
    es' = S.fromList es
    dps = M.fromAscList [(v, distancePartitionS vs es' v) | v <- vs]


{-
-- This is just fmap (\(p,bs) -> (p,bs,trace p)) t
equitablePartitionTracedSearchTree g@(G vs es) trace p = dfs [] p where
    dfs bs p = let p' = equitableRefinement' es' p
               in if all isSingleton p'
                  then T True (p',bs,trace p') []
                  else T False (p',bs,trace p') [dfs (b:bs) p'' | (b,p'') <- splits [] p']
    -- For now, we just split the first non-singleton cell we find
    splits ls (r:rs) | isSingleton r = splits (r:ls) rs
                     | otherwise = let ls' = reverse ls in [(x, ls' ++ [x]:xs:rs) | (x,xs) <- picks r]
    es' = S.fromList es
-}

-- Intended as a node invariant
trace1 p = map (\xs@(x:_) -> (x, length xs)) $ L.group $ L.sort $ map length p

equitablePartitionGraphSearchTree g@(G vs es) = equitablePartitionSearchTree g unitPartition
    where unitPartition = [vs]

-- The incidence graph has vertices that are coloured left (points) or right (blocks).
-- We are not interested in dualities (automorphisms that swap points and blocks), so we look for colour-preserving automorphisms
equitablePartitionIncidenceSearchTree g@(G vs es) = equitablePartitionSearchTree g lrPartition
    where (lefts, rights) = partitionEithers vs
          lrPartition = [map Left lefts, map Right rights]

leftLeaf (T False _ (t:ts)) = leftLeaf t
leftLeaf (T True (p,bs) []) = (concat p, reverse bs)
{-
leftSpine (T False x (t:ts)) = x : leftSpine t
leftSpine (T True x []) = [x]
-}
allLeaves (T False _ ts) = concatMap allLeaves ts
allLeaves (T True (p,bs) []) = [(concat p, reverse bs)]

{-
partitionTransversals tree = [fromPairs (zip canonical partition) | partition <- findTransversals tree] where
    (_,canonical) = leftLeaf tree
    findTransversals (T False _ (t:ts)) = concatMap (take 1 . findTransversals) ts ++ findTransversals t
    findTransversals (T True (_,partition) []) = [concat partition]

graphAuts5 = partitionTransversals . equitablePartitionGraphSearchTree
-}
-- NOT WORKING
partitionBSGS0 g@(G vs es) t = (bs, findLevels t) where
    (p1,bs) = leftLeaf t
    g1 = fromPairs $ zip p1 vs
    g1' = g1^-1
    es1 = S.fromList $ edges $ fmap (.^ g1) g -- the edges of the isomorph corresponding to p1. (S.fromList makes it unnecessary to call nf.)
    findLevels (T True (partition,_) []) = []
    findLevels (T False (partition,_) (t:ts)) =
        let hs = findLevels t
            -- TODO: It might be better to use the b that is added in t to find the cell that splits
            cell@(v:vs) = head $ filter (not . isSingleton) partition -- the cell that is going to split
        in findLevel v hs (zip vs ts)
    findLevel v hs ((v',t'):vts) = if v' `elem` v .^^ hs
                                   then findLevel v hs vts
                                   else let h = find1New t' in findLevel v (h++hs) vts
    findLevel _ hs [] = hs
    find1New (T False _ ts) = take 1 $ concatMap find1New ts
    -- There is a leaf for every aut, but not necessarily an aut for every leaf, so we must check we have an aut
    -- (For example, incidenceGraphPG 2 f8 has leaf nodes which do not correspond to auts.)
    find1New (T True (partition,_) []) = let h = fromPairs $ zip (concat partition) vs
                                             g' = fmap (.^ h) g
                                         in if all (`S.member` es1) (edges g') then [h*g1'] else []
    -- isAut h = all (`S.member` es') [e -^ h | e <- es]
    -- es' = S.fromList es

-- Given a partition search tree, return a base and strong generating set for graph automorphism group.
partitionBSGS g@(G vs es) t = (bs, findLevels t) where
    (canonical,bs) = leftLeaf t
    findLevels (T True (partition,_) []) = []
    findLevels (T False (partition,_) (t:ts)) =
        let hs = findLevels t
            -- TODO: It might be better to use the b that is added in t to find the cell that splits
            cell@(v:vs) = head $ filter (not . isSingleton) partition -- the cell that is going to split
        in findLevel v hs (zip vs ts)
    findLevel v hs ((v',t'):vts) = if v' `elem` v .^^ hs -- TODO: Memoize this orbit
                                   then findLevel v hs vts
                                   else let h = find1New t' in findLevel v (h++hs) vts
    findLevel _ hs [] = hs
    find1New (T False _ ts) = take 1 $ concatMap find1New ts
    -- Some leaf nodes correspond to different isomorphs of the graph, and hence don't yield automorphisms
    find1New (T True (partition,_) []) = let h = fromPairs $ zip canonical (concat partition)
                                         in filter isAut [h]
    isAut h = all (`S.member` es') [e -^ h | e <- es]
    es' = S.fromList es
-- The tree for g1 has leaf nodes of two different isomorphs, as does the tree for incidenceGraphPG 2 f8

-- Returns auts as Right, different isomorphs as Left
-- (Must be used with the tree which doesn't put singletons to end)
partitionBSGS3 g@(G vs es) t = (bs, findLevels t) where
    (p1,bs) = leftLeaf t
    findLevels (T True (partition,_) []) = []
    findLevels (T False (partition,_) (t:ts)) =
        let hs = findLevels t
            -- TODO: It might be better to use the b that is added in t to find the cell that splits
            cell@(v:vs) = head $ filter (not . isSingleton) partition -- the cell that is going to split
        in findLevel v hs (zip vs ts)
    findLevel v hs ((v',t'):vts) = if v' `elem` v .^^ rights hs
                                   then findLevel v hs vts
                                   else let h = find1New t' in findLevel v (h++hs) vts
    findLevel _ hs [] = hs
    find1New (T False _ ts) = take 1 $ concatMap find1New ts
    -- There is a leaf for every aut, but not necessarily an aut for every leaf, so we must check we have an aut
    -- (For example, incidenceGraphPG 2 f8 has leaf nodes which do not correspond to auts.)
    find1New (T True (partition,_) []) = let h = fromPairs $ zip p1 (concat partition)
                                         in if isAut h then [Right h] else [Left h]
    isAut h = all (`S.member` es') [e -^ h | e <- es]
    es' = S.fromList es
-- TODO: I think we are only justified in doing find1New (ie only finding 1) if we *do* find an aut.
-- If we don't, we should potentially keep looking in that subtree
-- (See section 6 of paper. If we find isomorphic leaves, then the two subtrees of their common parent are isomorphic,
-- so no need to continue searching the second.)


-- This is using a node invariant to do more pruning.
-- However, seems to be much slower on very regular graphs (where perhaps there is no pruning to be done)
-- (This suggests that perhaps using fmap is not good - perhaps a space leak?)
-- (Or perhaps it's just that calculating and comparing the node invariants is expensive)
-- TODO: Perhaps use something simpler, like just the number of cells in the partition
partitionBSGS2 g@(G vs es) t = (bs, findLevels t') where
    t' = fmap (\(p,bs) -> (p,bs,trace1 p)) t
    trace1 = length -- the number of cells in the partition
    (canonical,bs) = leftLeaf t
    findLevels (T True (partition,_,_) []) = []
    findLevels (T False (partition,_,_) (t:ts)) =
        let (T _ (_,_,trace) _) = t
            hs = findLevels t
            -- TODO: It might be better to use the b that is added in t to find the cell that splits
            cell@(v:vs) = head $ filter (not . isSingleton) partition -- the cell that is going to split
            vts = filter (\(_,T _ (_,_,trace') _) -> trace == trace') $ zip vs ts
        in findLevel v hs vts
    findLevel v hs ((v',t'):vts) = if v' `elem` v .^^ hs
                                   then findLevel v hs vts
                                   else let h = find1New t' in findLevel v (h++hs) vts
    findLevel _ hs [] = hs
    find1New (T False _ ts) = take 1 $ concatMap find1New ts
    -- There is a leaf for every aut, but not necessarily an aut for every leaf, so we must check we have an aut
    -- (For example, incidenceGraphPG 2 f8 has leaf nodes which do not correspond to auts.)
    -- (The graph g1, below, shows a simple example where this will happen.)
    find1New (T True (partition,_,_) []) = let h = fromPairs $ zip canonical (concat partition)
                                           in filter isAut [h]
    isAut h = all (`S.member` es') [e -^ h | e <- es]
    es' = S.fromList es


graphAuts7 g = (partitionBSGS g) (equitablePartitionGraphSearchTree g)

-- This is faster on kneser graphs, but slower on incidenceGraphPG
graphAuts8 g = (partitionBSGS g) (equitableDistancePartitionSearchTree g [vertices g])

-- This is a graph where the node invariant should cause pruning.
-- The initial equitable partition will be [[1..8],[9,10]], because it can do no better than distinguish by degree
-- However, vertices 1..4 and vertices 5..8 are in fact different (there is no aut that takes one set to the other),
-- so the subtrees starting 1..4 have a different invariant to those starting 5..8
g1 = G [1..10] [[1,2],[1,3],[1,9],[2,4],[2,10],[3,4],[3,9],[4,10],[5,6],[5,8],[5,9],[6,7],[6,10],[7,8],[7,9],[8,10]]

g1' = nf $ fmap (\x -> if x <= 4 then x+4 else if x <= 8 then x-4 else x) g1
-- G [1..10] [[1,2],[1,4],[1,9],[2,3],[2,10],[3,4],[3,9],[4,10],[5,6],[5,7],[5,9],[6,8],[6,10],[7,8],[7,9],[8,10]]

g2 = G [1..12] [[1,2],[1,4],[1,11],[2,3],[2,12],[3,4],[3,11],[4,12],[5,6],[5,8],[5,11],[6,9],[6,12],[7,8],[7,10],[7,11],[8,12],[9,10],[9,11],[10,12]]

-- NOT WORKING: This fails to find the isomorphism between g1 and g1' above.
-- Instead of using left leaf, we need to find the canonical isomorph, as described in the paper.
-- (In a graph where not all leaves lead to automorphisms, we might happen to end up with non-isomorphic left leaves)
maybeGraphIso g1 g2 = let (vs1,_) = (leftLeaf . equitablePartitionGraphSearchTree) g1
                          (vs2,_) = (leftLeaf . equitablePartitionGraphSearchTree) g2
                          f = M.fromList (zip vs1 vs2)
                      in if length vs1 == length vs2 && (nf . fmap (f M.!)) g1 == g2 then Just f else Nothing


-- AUTS OF INCIDENCE STRUCTURE VIA INCIDENCE GRAPH

-- This code is nearly identical to the corresponding graphAuts code, with two exceptions:
-- 1. We start by partitioning into lefts and rights.
-- This avoids left-right crossover auts, which while they are auts of the graph,
-- are not auts of the incidence structure
-- 2. When labelling the nodes, we filter out Right blocks, and unLeft the Left points
incidenceAutsDistancePartitionSearchTree g@(G vs es) = dfs [] (lrPart, lrPart) where
    dfs xys (srcPart,trgPart)
        | all isSingleton srcPart =
             let xys' = zip (concat srcPart) (concat trgPart)
             in T (isCompatible xys') (unLeft $ xys++xys') []
             -- Since the xys' are distance-compatible with the xys, they are certainly edge-compatible.
             -- However, we do need to check that the xys' are edge-compatible with each other.
        | otherwise = let (x:xs):srcCells = srcPart
                          yys   :trgCells = trgPart
                          srcPart' = intersectCells (xs : srcCells) (dps M.! x)
                      in T False (unLeft xys) -- the L.sort in the following line is so that we traverse vertices in natural order
                         [dfs ((x,y):xys) ((unzip . L.sort) (zip (filter (not . null) srcPart') (filter (not . null) trgPart')))
                         | (y,ys) <- picks yys,
                           let trgPart' = intersectCells (ys : trgCells) (dps M.! y),
                           map length srcPart' == map length trgPart']
    isCompatible xys = and [([x,x'] `S.member` es') == (L.sort [y,y'] `S.member` es') | (x,y) <- xys, (x',y') <- xys, x < x']
    (lefts, rights) = partitionEithers vs
    lrPart = [map Left lefts, map Right rights] -- Partition the vertices into left and right, to exclude crossover auts
    unLeft xys = [(x,y) | (Left x, Left y) <- xys] -- also filters out Rights
    es' = S.fromList es
    dps = M.fromList [(v, distancePartitionS vs es' v) | v <- vs]

-- |Given the incidence graph of an incidence structure between points and blocks
-- (for example, a set system),
-- @incidenceAuts g@ returns a strong generating set for the automorphism group of the incidence structure.
-- The generators are represented as permutations of the points.
-- The incidence graph should be represented with the points on the left and the blocks on the right.
incidenceAuts :: (Ord p, Ord b) => Graph (Either p b) -> [Permutation p]
incidenceAuts = filter (/= p []) . strongTerminals . incidenceAutsDistancePartitionSearchTree


-- TODO: Filter out rights, map unLeft - to bs and gs
incidenceAuts2 g = (partitionBSGS g) (equitablePartitionIncidenceSearchTree g)
    where unLeft (Left x) = x
          -- map (\g -> fromPairs . map (\(Left x, Left y) -> (x,y)) . filter (\(x,y) -> isLeft x) . toPairs) gs


-- GRAPH ISOMORPHISMS

-- !! not yet using equitable partitions, so could probably be more efficient

-- graphIsos :: (Ord a, Ord b) => Graph a -> Graph b -> [[(a,b)]]
graphIsos g1 g2
    | length cs1 /= length cs2 = []
    | otherwise = graphIsos' cs1 cs2
    where cs1 = map (inducedSubgraph g1) (components g1)
          cs2 = map (inducedSubgraph g2) (components g2)
          graphIsos' (ci:cis) cjs =
              [iso ++ iso' | (cj,cjs') <- picks cjs,
                             iso <- graphIsosCon ci cj,
                             iso' <- graphIsos' cis cjs']
          graphIsos' [] [] = [[]]

-- isos between connected graphs
graphIsosCon g1 g2 
    | isConnected g1 && isConnected g2
        = concat [dfs [] (distancePartition g1 v1) (distancePartition g2 v2)
                 | v1 <- take 1 (vertices g1), v2 <- vertices g2]
                 -- the take 1 handles the case where g1 is the null graph
    | otherwise = error "graphIsosCon: either or both graphs are not connected"
    where dfs xys p1 p2
              | map length p1 /= map length p2 = []
              | otherwise =
                  let p1' = filter (not . null) p1
                      p2' = filter (not . null) p2
                  in if all isSingleton p1'
                     then let xys' = xys ++ zip (concat p1') (concat p2')
                          in if isCompatible xys' then [xys'] else []
                     else let (x:xs):p1'' = p1'
                              ys:p2'' = p2'
                          in concat [dfs ((x,y):xys)
                                         (intersectCells (xs : p1'') (dps1 M.! x))
                                         (intersectCells (ys': p2'') (dps2 M.! y))
                                         | (y,ys') <- picks ys]
          isCompatible xys = and [([x,x'] `S.member` es1) == (L.sort [y,y'] `S.member` es2) | (x,y) <- xys, (x',y') <- xys, x < x']
          dps1 = M.fromAscList [(v, distancePartitionS vs1 es1 v) | v <- vs1]
          dps2 = M.fromAscList [(v, distancePartitionS vs2 es2 v) | v <- vs2]
          -- dps1 = M.fromList [(v, distancePartition g1 v) | v <- vertices g1]
          -- dps2 = M.fromList [(v, distancePartition g2 v) | v <- vertices g2]
          vs1 = vertices g1
          vs2 = vertices g2
          es1 = S.fromList $ edges g1
          es2 = S.fromList $ edges g2


-- |Are the two graphs isomorphic?
isGraphIso :: (Ord a, Ord b) => Graph a -> Graph b -> Bool
isGraphIso g1 g2 = (not . null) (graphIsos g1 g2)
-- !! If we're only interested in seeing whether or not two graphs are iso,
-- !! then the cost of calculating distancePartitions may not be warranted
-- !! (see Math.Combinatorics.Poset: orderIsos01 versus orderIsos)


-- the following differs from graphIsos in only two ways
-- we avoid Left, Right crossover isos, by insisting that a Left is taken to a Left (first two lines)
-- we return only the action on the Lefts, and unLeft it
-- incidenceIsos :: (Ord p1, Ord b1, Ord p2, Ord b2) =>
--     Graph (Either p1 b1) -> Graph (Either p2 b2) -> [[(p1,p2)]]

incidenceIsos g1 g2
    | length cs1 /= length cs2 = []
    | otherwise = incidenceIsos' cs1 cs2
    where cs1 = map (inducedSubgraph g1) (filter (not . null . lefts) $ components g1)
          cs2 = map (inducedSubgraph g2) (filter (not . null . lefts) $ components g2)
          incidenceIsos' (ci:cis) cjs =
              [iso ++ iso' | (cj,cjs') <- picks cjs,
                             iso <- incidenceIsosCon ci cj,
                             iso' <- incidenceIsos' cis cjs']
          incidenceIsos' [] [] = [[]]

incidenceIsosCon g1 g2
    | isConnected g1 && isConnected g2
        = concat [dfs [] (distancePartition g1 v1) (distancePartition g2 v2)
                 | v1@(Left _) <- take 1 (vertices g1), v2@(Left _) <- vertices g2]
                 -- g1 may have no vertices
    | otherwise = error "incidenceIsos: one or both graphs not connected"
    where dfs xys p1 p2
              | map length p1 /= map length p2 = []
              | otherwise =
                  let p1' = filter (not . null) p1
                      p2' = filter (not . null) p2
                  in if all isSingleton p1'
                     then let xys' = xys ++ zip (concat p1') (concat p2')
                          in if isCompatible xys' then [[(x,y) | (Left x, Left y) <- xys']] else []
                     else let (x:xs):p1'' = p1'
                              ys:p2'' = p2'
                          in concat [dfs ((x,y):xys)
                                         (intersectCells (xs : p1'') (dps1 M.! x))
                                         (intersectCells (ys': p2'') (dps2 M.! y))
                                         | (y,ys') <- picks ys]
          isCompatible xys = and [([x,x'] `S.member` es1) == (L.sort [y,y'] `S.member` es2) | (x,y) <- xys, (x',y') <- xys, x < x']
          dps1 = M.fromList [(v, distancePartition g1 v) | v <- vertices g1]
          dps2 = M.fromList [(v, distancePartition g2 v) | v <- vertices g2]
          es1 = S.fromList $ edges g1
          es2 = S.fromList $ edges g2

-- |Are the two incidence structures represented by these incidence graphs isomorphic?
isIncidenceIso :: (Ord p1, Ord b1, Ord p2, Ord b2) =>
     Graph (Either p1 b1) -> Graph (Either p2 b2) -> Bool
isIncidenceIso g1 g2 = (not . null) (incidenceIsos g1 g2)



