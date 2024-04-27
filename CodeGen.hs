module CodeGen where

import TreeDecomposition
import Data.Map hiding (map,take)
import Data.List (intercalate)
k=2
-- types of node in the tree
data TreeNode = FuseNode | ForgetNode Int | VertexNode Int | EdgeNode Int Int  deriving (Eq,Ord)
instance Show TreeNode where
 show (FuseNode) = "fusion"
 show (ForgetNode i) = "forget"++ (show i)
 show (VertexNode n) = "vertex_" ++ (show n)
 show (EdgeNode u v) = "edge_" ++ (show u) ++ "_" ++ (show v) 
-- show (Empty)        = "dummy"
-- set encoding used in the mona code :  node type|number 1|number2
data BinaryCoding = Bit1 | Bit2 | Num1 Int | Num2 Int deriving (Eq, Ord)
instance Show BinaryCoding where
 show (Bit1) = "bit1"
 show (Bit2) = "bit2"
 show (Num1 n) = "num1_bit"++(show n)
 show (Num2 n) = "num2_bit"++(show n)

type Zipper a = (a, String)


--bits
log2 n = length $ binary n

binary :: Int -> [Int]
binary 0 = []
binary n = binary (div n 2) ++ [(mod n 2)] 

--zeroPad xs n | length xs >=n =x
--		| otherwise = n - (length xs)

lpad m xs = replicate (m - length ys) 0 ++ ys
    where ys = take m xs

binPos [] _ = []
binPos (1 :xs) i = i : binPos xs (i+1)
binPos (0 :xs) i = binPos xs (i+1)

makeNum1 n i = map Num1 $ binPos (lpad n $ binary i) 0
makeNum2 n i = map Num2 $ binPos (lpad n $ binary i) 0

encode :: Int-> TreeNode -> [BinaryCoding]
encode _ (FuseNode) = [Bit1,Bit2]
encode n (ForgetNode i) = makeNum1 n i
encode n (EdgeNode u v) = [Bit2] ++ makeNum1 n u ++ makeNum2 n v
encode n (VertexNode v) = [Bit1] ++ makeNum1 n v
--encode (Empty) = [Empty]
---

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
emptyMapping2 k = map (pair []) $ [Bit1,Bit2] ++[Num1 i| i<-[0..(k -1)]] ++ [Num2 i | i <- [0..(k-1)]]

makeMapping :: Int -> Zipper (TreeDecomp Constant) -> Map BinaryCoding [String]
makeMapping k ts = fromListWith (++) $ ( expand $ listify $ makeLayer ts) ++ emptyMapping2 n where
  n = log2 k
  listify =  map (\(x,y)->(x,[y])) 
  expand [] = []
  expand ((x,y):xs) = map (\w -> (w,y) ) (encode n x) ++ expand xs

makeCode :: [(BinaryCoding, [String])] -> [String]
makeCode [] = []
makeCode ((n,[]):xs) = ("empty("++(show n) ++");") :( makeCode xs)
makeCode ((n,ss):xs) = ((show n) ++" = {" ++ (pprintList ss) ++"};") : ( makeCode xs)

universe t = map snd $ makeLayer t
makeCode' t = "$ = {" ++  (pprintList $ universe t ) ++"};"



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

