module Main where
import TreeDecomposition
import ParseFiles
import CodeGen
import System.Environment
--import Data.Tree (Tree(Node))
import qualified Data.Tree as Tree (drawTree, Tree(Node))
import qualified Data.Map as Map

tree (Node a) = Tree.Node (show a) []
tree (Forget k t) = Tree.Node ("forget "++ (show k)) [tree t]
tree (Fuse t t') = Tree.Node ("fuse") [tree t, tree t']

leaves (Node a) = [ a]
leaves (Forget k t) = leaves t
leaves (Fuse t t') = leaves t ++ leaves t'

findzeros (a,(v,e)) =(zs,ws) where zs = Map.filter ( ==0) a;ws = filter (\(x,y) -> (a Map.! x == 0) && (a Map.! y == 0)) e

printTree t = do putStrLn $ Tree.drawTree $ tree $ t


main = do
	args <- getArgs
	g <- readGraph $ args !! 0--"test2.gr"
	t <- readTreeD $ args !! 1-- "test2.tw"
	let k = case t of (a,b,c) -> (a)
	let td = decompose g (clean t)
--	let gc = decompose'' g (clean t)
--	let gc2 = findzeros gc
--	print (case t of (a,b,c) -> b)
--	print "----- yo ---- "
--	print $ gc
--	putStrLn $ Tree.drawTree $ tree $ td
	putStrLn $ toMona k td

