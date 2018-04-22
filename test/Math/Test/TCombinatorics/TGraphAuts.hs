-- Copyright (c) 2011, David Amos. All rights reserved.

module Math.Test.TCombinatorics.TGraphAuts where

import Data.List as L
import Math.Core.Field hiding (f7)
import Math.Core.Utils (combinationsOf)
import Math.Algebra.Group.PermutationGroup as P
import Math.Algebra.Group.RandomSchreierSims as SS
import Math.Combinatorics.Graph as G
import Math.Combinatorics.GraphAuts
import Math.Combinatorics.Matroid as M
import Math.Combinatorics.FiniteGeometry

import qualified Math.Algebra.Field.Extension as F

import Test.HUnit


testlistGraphAuts = TestList [
    testlistGraphAutsOrder,
    testlistGraphAutsGroup,
    testlistGraphAutsComplement,
    testlistIncidenceAutsOrder,
    testlistGraphIsos,
    testlistIsGraphIso,
    testlistIncidenceIsos,
    testlistVertexTransitive,
    testlistNotVertexTransitive,
    testlistEdgeTransitive,
    testlistNotEdgeTransitive,
    testlistArcTransitive,
    testlistNotArcTransitive,
    testlist2ArcTransitive,
    testlistNot2ArcTransitive,
    testlist4ArcTransitive,
    testlistDistanceTransitive,
    testlistNotDistanceTransitive
    ]


-- We know the expected order of the graph automorphism group
testcaseGraphAutsOrder desc g n = TestCase $
    assertEqual ("order " ++ desc) n (orderSGS $ graphAuts g)

testlistGraphAutsOrder = TestList [
    let g = G [1..6] [[1,2],[3,4],[5,6]] in
        testcaseGraphAutsOrder (show g) g 48, -- 2*2*2*3!
    testcaseGraphAutsOrder "cube" cube 48,
    testcaseGraphAutsOrder "dodecahedron" dodecahedron 120
    ]


induced bs g = fromPairs [(b, b -^ g) | b <- bs]

-- We know the expected group of graph automorphisms
testcaseGraphAutsGroup desc graph group = TestCase $
    assertEqual ("group " ++ desc) (elts $ graphAuts graph) (elts $ group)

testlistGraphAutsGroup = TestList [
    testcaseGraphAutsGroup "nullGraph 0" (nullGraph 0) [],
    testcaseGraphAutsGroup "nullGraph 1" (nullGraph 1) (_S 1),
    testcaseGraphAutsGroup "nullGraph 2" (nullGraph 2) (_S 2),
    testcaseGraphAutsGroup "nullGraph 3" (nullGraph 3) (_S 3),
    testcaseGraphAutsGroup "k 3" (k 3) (_S 3),
    testcaseGraphAutsGroup "k 4" (k 4) (_S 4),
    testcaseGraphAutsGroup "k 5" (k 5) (_S 5),
    testcaseGraphAutsGroup "c 4" (c 4) (_D 8),
    testcaseGraphAutsGroup "c 5" (c 5) (_D 10),
    let graph = G [1..3] [[1,2],[2,3]] in
        testcaseGraphAutsGroup (show graph) graph [p [[1,3]]], -- regression test
    let graph = G [1..6] [[2,3],[4,5],[5,6]] in
        testcaseGraphAutsGroup (show graph) graph [p [[2,3]], p [[4,6]]],
    testcaseGraphAutsGroup "petersen" petersen (map (induced $ combinationsOf 2 [1..5]) $ _S 5)
    ]


-- The automorphisms of the graph should be the same as the auts of its complement
testcaseGraphAutsComplement desc g = TestCase $
    assertEqual ("complement " ++ desc) (elts $ graphAuts g) (elts $ graphAuts $ complement g)
-- the algorithm may not find the same set of generators, so we have to compare the elements

testlistGraphAutsComplement = TestList [
    testcaseGraphAutsComplement "k 3" (k 3),
    testcaseGraphAutsComplement "kb 2 3" (kb 2 3), -- complement is not connected
    testcaseGraphAutsComplement "kb 3 3" (kb 3 3), -- complement is not connected, but components can be swapped
    testcaseGraphAutsComplement "kt 2 3 3" (kt 2 3 3),
    testcaseGraphAutsComplement "kt 2 3 4" (kt 2 3 4),
    testcaseGraphAutsComplement "kt 3 3 3" (kt 3 3 3)
    ]

kt a b c = graph (vs,es)
    where vs = [1..a+b+c]
          es = L.sort $ [[i,j] | i <- [1..a], j <- [a+1..a+b] ]
                     ++ [[i,k] | i <- [1..a], k <- [a+b+1..a+b+c] ]
                     ++ [[j,k] | j <- [a+1..a+b], k <- [a+b+1..a+b+c] ]

-- We know the expected order of the incidence structure automorphism group
testcaseIncidenceAutsOrder desc g n = TestCase $
    assertEqual ("incidence order " ++ desc) n (P.order $ incidenceAuts g)

-- We use matroids as our incidence structure just because we have a powerful library for constructing them
testlistIncidenceAutsOrder = TestList [
    testcaseIncidenceAutsOrder "pg2 f2 (B)" (incidenceGraphB $ matroidPG 2 f2) 168,
    testcaseIncidenceAutsOrder "pg2 f2 (C)" (incidenceGraphC $ matroidPG 2 f2) 168,
    testcaseIncidenceAutsOrder "pg2 f2 (H)" (incidenceGraphH $ matroidPG 2 f2) 168,
    testcaseIncidenceAutsOrder "u 1 3 (B)" (incidenceGraphB $ u 1 3) 6, -- not connected
    testcaseIncidenceAutsOrder "u 1 3 (C)" (incidenceGraphC $ u 1 3) 6,
    testcaseIncidenceAutsOrder "u 1 3 (H)" (incidenceGraphH $ u 1 3) 6, -- not connected
    testcaseIncidenceAutsOrder "u 2 3 `dsum` u 2 3 (H)" (incidenceGraphH $ u 2 3 `dsum` u 2 3) 72, -- 6*6*2
    testcaseIncidenceAutsOrder "u 2 3 `dsum` u 2 3 (C)" (incidenceGraphC $ u 2 3 `dsum` u 2 3) 72, -- not connected
    testcaseIncidenceAutsOrder "u 2 3 `dsum` u 3 4 (H)" (incidenceGraphH $ u 2 3 `dsum` u 3 4) 144, -- 6*24
    testcaseIncidenceAutsOrder "u 2 3 `dsum` u 3 4 (C)" (incidenceGraphC $ u 2 3 `dsum` u 3 4) 144 -- not connected
    ]


testcaseGraphIsos g1 g2 isos = TestCase $
    assertEqual (show (g1,g2)) isos (graphIsos g1 g2)

testlistGraphIsos = TestList [
    testcaseGraphIsos (G [1,2] []) (G [3,4] []) [[(1,3),(2,4)],[(1,4),(2,3)]],
    testcaseGraphIsos (G [1,2,3] [[1,2]]) (G [4,5,6] [[5,6]]) [[(1,5),(2,6),(3,4)],[(1,6),(2,5),(3,4)]]
    ]


testcaseIsGraphIso g1 g2 = TestCase $
    assertBool (show (g1,g2)) $ isGraphIso g1 g2

testlistIsGraphIso = TestList [
    testcaseIsGraphIso (nullGraph') (nullGraph')
    ]


testcaseIncidenceIsos g1 g2 isos = TestCase $
    assertEqual (show (g1,g2)) isos (incidenceIsos g1 g2)

testlistIncidenceIsos = TestList [
    testcaseIncidenceIsos (G [Left 1, Right 2] []) (G [Left 3, Right 4] []) [[(1,3)]],
    testcaseIncidenceIsos (G [Left 1, Left 2, Right 1] [[Left 1, Right 1]])
                          (G [Left 3, Left 4, Right 4] [[Left 4, Right 4]])
                          [[(1,4),(2,3)]]
    ]

testcaseVertexTransitive (desc, graph) = TestCase $
    assertBool ("isVertexTransitive " ++ desc) $ isVertexTransitive graph

testlistVertexTransitive = TestList $ map testcaseVertexTransitive [
    -- because we're mapping, these all have to be of same type, hence Graph Int
    ("(q 3)", q 3),
    ("(q 4)", q 4),
    ("petersen", G.to1n petersen)
    ]

testcaseNotVertexTransitive (desc, graph) = TestCase $
    assertBool ("not isVertexTransitive " ++ desc) $ (not . isVertexTransitive) graph

testlistNotVertexTransitive = TestList $ map testcaseNotVertexTransitive [
    ("(kb 2 3)", G.to1n $ kb 2 3),
    ("(kb 3 4)", G.to1n $ kb 3 4),
    ("regular not vertex transitive" , G [(1::Int)..8] [[1,2],[1,3],[1,8],[2,3],[2,4],[3,5],[4,5],[4,6],[5,7],[6,7],[6,8],[7,8]])
    ]


testcaseEdgeTransitive (desc, graph) = TestCase $
    assertBool ("isEdgeTransitive " ++ desc) $ isEdgeTransitive graph

testlistEdgeTransitive = TestList $ map testcaseEdgeTransitive [
    ("(kb 2 3)", kb 2 3),
    ("(kb 3 4)", kb 3 4)
    ]

testcaseNotEdgeTransitive (desc, graph) = TestCase $
    assertBool ("not isEdgeTransitive " ++ desc) $ (not . isEdgeTransitive) graph

testlistNotEdgeTransitive = TestList $ map testcaseNotEdgeTransitive [
    ("pyramid 4", pyramid 4),
    ("pyramid 5", pyramid 5),
    ("prism 3", G.to1n $ prism 3),
    ("prism 5", G.to1n $ prism 5)
    ]
    where pyramid n = let G vs es = c n in graph (0:vs, [[0,v] | v <- vs] ++ es)


testcaseArcTransitive (desc, graph) = TestCase $
    assertBool ("isArcTransitive " ++ desc) $ isArcTransitive graph

testlistArcTransitive = TestList $ map testcaseArcTransitive [
    -- Godsil and Royle, p60 - j v k i is arc-transitive
    ("(j 4 2 0)", j 4 2 0),
    ("(j 5 2 0)", j 5 2 0),
    ("(j 5 2 1)", j 5 2 1)
    ]

testcaseNotArcTransitive (desc, graph) = TestCase $
    assertBool ("not isArcTransitive " ++ desc) $ (not . isArcTransitive) graph

testlistNotArcTransitive = TestList $ map testcaseNotArcTransitive [
    ("kb 3 2", kb 3 2),
    ("kb 4 3", kb 4 3)
    ]


testcase2ArcTransitive (desc, graph) = TestCase $
    assertBool ("is2ArcTransitive " ++ desc) $ is2ArcTransitive graph

testlist2ArcTransitive = TestList $ map testcase2ArcTransitive [
    -- Godsil and Royle, p60 - j (2k+1) k 0 is 2-arc-transitive
    ("(j 3 1 0)", j 3 1 0),
    ("(j 5 2 0)", j 5 2 0),
    ("(j 7 3 0)", j 7 3 0)
    ]

testcaseNot2ArcTransitive (desc, graph) = TestCase $
    assertBool ("not is2ArcTransitive " ++ desc) $ (not . is2ArcTransitive) graph

testlistNot2ArcTransitive = TestList $ map testcaseNot2ArcTransitive [
    -- because a 2-arc can be two sides of a triangle, or not, so they are not all alike
    ("octahedron", octahedron),
    ("icosahedron", icosahedron)
    ]


testcase4ArcTransitive (desc, graph) = TestCase $
    assertBool ("is4ArcTransitive " ++ desc) $ is4ArcTransitive graph

testlist4ArcTransitive = TestList $ map testcase4ArcTransitive [
    -- Godsil and Royle, p80-1
    ("PG(2,F2)", G.to1n $ incidenceGraphPG 2 f2),
    ("PG(2,F3)", G.to1n $ incidenceGraphPG 2 f3),
    ("PG(2,F4)", G.to1n $ incidenceGraphPG 2 f4)
    ]


testcaseDistanceTransitive (desc, graph) = TestCase $
    assertBool ("isDistanceTransitive " ++ desc) $ isDistanceTransitive graph

testlistDistanceTransitive = TestList $ map testcaseDistanceTransitive [
    ("(kb 3 3)", G.to1n $ kb 3 3),
    ("(kb 4 4)", G.to1n $ kb 4 4),
    ("(q 3)", G.to1n $ q 3),
    ("(q 4)", G.to1n $ q 4),
    ("petersen", G.to1n $ petersen),
    -- Godsil and Royle, p67 - j v k (k-1) and j (2k+1) (k+1) 0 are distance-transitive
    ("(j 3 2 1)", G.to1n $ j 3 2 1),
    ("(j 4 2 1)", G.to1n $ j 4 2 1),
    ("(j 5 3 2)", G.to1n $ j 5 3 2)
    -- ("(j 3 2 0)", G.to1n $ j 3 2 0),
    -- ("(j 5 3 0)", G.to1n $ j 5 3 0),
    -- ("(j 7 4 0)", G.to1n $ j 7 4 0)
    ]

testcaseNotDistanceTransitive (desc, graph) = TestCase $
    assertBool ("not isDistanceTransitive " ++ desc) $ (not . isDistanceTransitive) graph

testlistNotDistanceTransitive = TestList $ map testcaseNotDistanceTransitive [
    ("(prism 3)", prism 3),
    -- not prism 4, which is the cube
    ("(prism 5)", prism 5)
    ]

