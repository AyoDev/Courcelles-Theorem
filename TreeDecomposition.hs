module TreeDecomposition where
import qualified Data.Map as Map
import Data.List
import Data.Maybe (fromJust)
import qualified Data.Tree as Tree

-- algebraic tree decomposition in a 
data TreeDecomp a = Node a | Fuse (TreeDecomp a) (TreeDecomp a) | Forget Colour (TreeDecomp a) deriving Show

-- we only need to define single edge and single vertex graphs, I will mostly refer to these as primitives
data Constant = CEdge Edge | CVertex Vertex

instance Show Constant where
 show (CEdge   e) = show e
 show (CVertex v) = show v

-- Rooted trees
data Tree a = Leaf a | INode a [Tree a] deriving Show
type Tree' = Tree Vertex
type Bag = [Vertex]
type Bags = Map.Map Vertex Bag
type AdjList = Bags
type TrGraph = (Int,Bags, Graph) 

type Graph =([Vertex], [Edge])

type Colouring = Map.Map Vertex Colour
type SGraph = (Colouring, Graph)

type Vertex = Int
type Edge = (Vertex,Vertex)
type Colour = Int

--
instance Functor Tree where
	fmap f (Leaf a) = Leaf (f a)
	fmap f (INode a xs) = INode (f a) $ map (fmap f) xs

--useful
tMap :: (a -> b) -> (a,a) -> (b,b)
tMap f (x,y) = (f x, f y)

pair :: a -> b -> (b,a)
pair a b = (b,a)

diff a b = nub $ (a\\b) ++ (b\\a)

makeEdge :: Edge -> Constant
makeEdge (x,y) = CEdge (x',y') where x' = min x y; y' = max x y

--graph setup
vertices = fst
edges = snd

vertex :: Tree' -> Vertex
vertex (Leaf a) = a
vertex (INode a _ ) = a

colouring = fst
v `incident` e@(e1,e2) = v==e1 || v==e2
v `neighbour`e@(e1,e2)  | v==e1 = e2
	
		| v==e2 = e1

neighbours :: Graph -> Vertex -> [Vertex]
neighbours (vs,es) v = map (neighbour v) $  filter (v `incident`) es



-- whole lotta red (colouring helper functions)
sColour :: SGraph -> Graph
sColour (naming, (vs,es)) = (vColour naming vs, eColour naming es)

colourVertex naming x = Map.findWithDefault (-1) x naming
colourEdge naming  =  tMap (naming Map.!)
colourConstant naming (CEdge e) = CEdge $ colourEdge naming e
colourConstant naming (CVertex v) = CVertex $ colourVertex naming v 

vColour :: Colouring -> [Vertex] -> [Vertex]
vColour naming vs = map (colourVertex naming) vs
eColour :: Colouring -> [Edge] -> [Edge]
eColour naming es = map (colourEdge naming) es
cColour :: Colouring -> [Constant] -> [Constant]
cColour naming cs = map (colourConstant naming) cs
colour :: Colouring -> Graph -> Graph
colour m g = sColour (m,g)

-- remove duplicates in bags, 
trimBags :: Bags -> Bags
trimBags = Map.map (nub)

clean :: TrGraph -> TrGraph
clean (k,b,g) = (k, trimBags b, g)
-- Adjacency Lists. used to implement basic linear time graph/tree algorithms.
makeAdjList :: Graph -> AdjList
makeAdjList (v,e) = edge2adjList v e

edge2adjList :: [Vertex] -> [Edge] -> AdjList
edge2adjList vs [] = Map.fromList $ map (pair []) vs
edge2adjList vs ((x,y):xs) = Map.adjust (y:) x $ Map.adjust (x:) (y) $ edge2adjList vs xs

-- turns adjeceny list to rooted directed tree (arborecense)
makeTree :: Vertex -> Vertex ->  AdjList -> Tree'
makeTree p v a | (a Map.! v) \\ [p] == [] = Leaf v -- a should at least be [] 
             | otherwise = INode v $ map (\x -> makeTree v x a )  $ (a Map.! v) \\ [p]
---algo stuff
-- the main algorithm 
-- converts bag based tree decomposition to algebraic tree decomposition of primitives
decompose :: Graph -> TrGraph -> TreeDecomp Constant
decompose g t'@(k,b,t) = fixForget $ convert $  makeDecomp (greedyColour t' tdTree ,g) t' tdTree where tdTree = (makeTree (-1) root aList); aList = makeAdjList t; root = head $ Map.keys aList 

decompose'' g t'@(k,b,t) = (greedyColour t' tdTree ,g) where tdTree = (makeTree (-1) root aList); aList = makeAdjList t; root = head $ Map.keys aList 

-- but first convert to tree decomp of k-sourced graphs
-- does above conversion for reall
makeDecomp :: SGraph -> TrGraph -> Tree' -> TreeDecomp SGraph
makeDecomp g' (k,b,g) (Leaf v) = Node $ induceGraph g' (b Map.! v)
makeDecomp g' t@(k,b,g) (INode v xs) = fuseAll $ map (\x -> Fuse (Node $ induceGraph g' bv) $ forget (colDiff (colouring g') bv (b Map.! (vertex x))) $ makeDecomp g' t x) xs where bv = b Map.! v



fixForget t = forget (unforgotten t) t

-- finds all unforgotten nodes in a tree decomposition (of coloured primitives)
-- assumes the only such nodes are those from the root of the original tree decomposition
unforgotten :: TreeDecomp Constant -> [Colour]
unforgotten (Node v) = nodesInConstant v
unforgotten (Forget k t) = unforgotten t \\ [k]
unforgotten (Fuse t1 t2) = nub $ unforgotten t1 ++ unforgotten t2

nodesInConstant :: Constant -> [Colour]
nodesInConstant (CEdge (u,v)) = [u,v]
nodesInConstant (CVertex v) = [v]

colDiff :: Colouring -> Bag -> Bag -> [Colour]
colDiff c' b1 b2 = nub $ vColour c' $ b1 `diff` b2

greedyColour :: TrGraph -> Tree' -> Colouring
greedyColour (k,b,t) t' = gColour k  (fmap (b Map.!) t') Map.empty 

gColour :: Int -> Tree Bag -> Colouring -> Colouring
gColour k (Leaf a) c' = gColour k (INode a [] ) c'
gColour k (INode x xs) c' = Map.unions $ [c''] ++ map (\y -> gColour k y c'') xs
	where 
	 c'' = Map.union c' (Map.fromList $ zip uncoloured unusedColours) 
	 usedColours = nub (vColour c' x)
	 unusedColours = [0..k] \\ usedColours
	 uncoloured= filter (flip Map.notMember c') x  


forget :: [Colour] -> TreeDecomp a -> TreeDecomp a 
forget [] = id
forget (x:xs) = (Forget x) . (forget xs)

induceGraph :: SGraph -> Bag -> SGraph
induceGraph (c,(vs,es)) b = (c, (b,es')) where es' = filter (\(x,y) -> (x `elem` b) && (y `elem` b)) es


-- conversion
-- (1) every sourced graph can be converted to a tree decomposition of coloured 'primitives' (single edge or single vertex)
-- (2) as a result a tree decomposition on sourced graphs can be converted to a tree decomposition on 'primitives'

-- does the above coversion (1)
convert :: TreeDecomp SGraph -> TreeDecomp Constant
convert (Node g) = convert' g
convert (Forget k g) = Forget k $ convert g
convert (Fuse g1 g2) = Fuse (convert g1) (convert g2)

-- does the above conversion (2)
-- assumes well formed graph
convert' :: SGraph -> TreeDecomp Constant
convert' g'@(naming, graph) = case findUncolouredVertex g' of-- checks if there is an uncoloured vertex
				Nothing -> fusePrimitives g' -- if all vertices are coloured just fuse all primitives
--				otherwise there should only be 1 uncoloured vertex, so we give it a (valid) colour and forget it. 
				Just v  -> fuseList  c $ tMap (cColour naming') $ splitByColour g' c  where 
													c =findValidColour naming $ vColour naming $ neighbours graph v;
													naming' = Map.insert v c naming

fuseList c (xs,ys) = fuseConstants xs `Fuse` (Forget c $ fuseConstants ys)

-- looks for an uncoloured node
findUncolouredVertex :: SGraph -> Maybe Vertex
findUncolouredVertex (m,g) = find (flip Map.notMember m) $ vertices g 

-- finds a colour (from the colouring) not in the given list
findValidColour :: Colouring -> [Colour] -> Colour
findValidColour naming xs = fromJust $ find (not.(`elem` xs)) $ Map.elems naming

-- partitions edges based on containing or not containing a colour
splitByColour :: SGraph -> Colour -> ([Constant],[Constant])
splitByColour (m,g) c = partition (hasColour m c) (primitives g) 

hasColour :: Colouring -> Colour -> Constant -> Bool
hasColour m c (CEdge (x,y)) = Map.lookup x m == Just c || Map.lookup y m == Just c
hasColour m c (CVertex x) = Map.lookup x m == Just c 

-- does conversion (1) by fusing all primitives
-- assumes all nodes are coloured
fusePrimitives :: SGraph -> TreeDecomp Constant
fusePrimitives g' =  fuseConstants $ primitives $ sColour g'

-- find vertices with no edges
findLonely :: Graph -> [Vertex]
findLonely  = Map.keys . Map.filter null . makeAdjList 

-- get all primitives of a graph (edges + lone vertices)
primitives :: Graph -> [Constant]
primitives g = map makeEdge (edges g) ++ map CVertex (findLonely g)

fuseConstants :: [Constant] -> TreeDecomp Constant
fuseConstants xs = fuseAll $ map Node xs

-- fuses all the tree decompositions in a list
fuseAll :: [TreeDecomp a] -> TreeDecomp a
fuseAll [a] = a
fuseAll (a:as) = Fuse a $ fuseAll as
