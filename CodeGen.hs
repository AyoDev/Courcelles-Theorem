module CodeGen where

import TreeDecomposition
import Data.Map hiding (map)
import Data.List (intercalate)
k=2
-- types of node in the tree
data TreeNode = FuseNode | ForgetNode Int | VertexNode Int | EdgeNode Int Int | Empty deriving (Eq,Ord)
instance Show TreeNode where
 show (FuseNode) = "fusion"
 show (ForgetNode i) = "forget"++ (show i)
 show (VertexNode n) = "vertex_" ++ (show n)
 show (EdgeNode u v) = "edge_" ++ (show u) ++ "_" ++ (show v) 
 show (Empty)        = "dummy"

type Zipper a = (a, String)

extract :: Zipper (TreeDecomp Constant) -> Zipper TreeNode
extract (Node (CVertex a),s) = (VertexNode a,s)
extract (Node (CEdge (a,b)),s) = (EdgeNode a b,s) 
extract (Forget k _,s) = (ForgetNode k, s)
extract (Fuse _ _,s) = (FuseNode,s)


children :: Zipper (TreeDecomp Constant) -> [Zipper (TreeDecomp Constant)]
children (Fuse a b, s) = [(a,s++"0"), (b,s++"1")]
children (Forget k t, s) = [(t,s++"0")]
children _ = []

makeLayer :: Zipper (TreeDecomp Constant) -> [Zipper TreeNode]
makeLayer ts = extract ts : ( concat $ map makeLayer $  children ts)

emptyMapping k = map (pair []) $ [FuseNode] ++[ForgetNode i| i<-[0..k]] ++ [EdgeNode i j| i<-[0..k],j<-[(i+1)..k]] ++[VertexNode i | i <- [0..k]]

makeMapping :: Int -> Zipper (TreeDecomp Constant) -> Map TreeNode [String]
makeMapping k ts = fromListWith (++) $ (listify $ makeLayer ts) ++ emptyMapping k where
  listify =  map (\(x,y)->(x,[y])) 

makeCode :: [(TreeNode, [String])] -> [String]
makeCode [] = []
makeCode ((n,[]):xs) = ("empty("++ (show n) ++");") : ( makeCode xs)
makeCode ((n,ss):xs) = ((show n) ++" = {" ++ (pprintList ss) ++"};") : ( makeCode xs)

mapAssert = map ("assert " ++)

pprintList xs = intercalate ", " $ map toPos xs 

-- [...] -->  ...
trimBrackets  =tail.init 

toPos "." = "root"
toPos ('.':xs) = "root."++xs

------testing-------
t = (2,fromList [(1,[1,2]),(2,[2,3]),(3,[3,4])],([1,2,3],[(1,2),(2,3)]))
g = ([1,2,3,4],[(1,2),(2,3)])
td = decompose g t
toMap = makeMapping -- . makeLayer
toZipper z tt = (tt,z)
toMona k = unlines . mapAssert .makeCode . toList .makeMapping k . toZipper "." 
