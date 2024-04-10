module ParseFiles where 
import TreeDecomposition
--import Text.Parsec
import qualified Data.Map as Map
import Data.List

readInt :: String -> Int
readInt = read
readInts = map readInt

fmap2 :: (b->c) ->  (a,b) -> (a,c)
fmap2 = fmap

parseGraph :: File -> Graph
parseGraph  = rG. pG-- i([1..k],edges) where tup = pG f; info = head $ fst tup;k = readInt $ info!!2; edges = toTuple $ snd tup

parseTDcmp :: File -> TrGraph
parseTDcmp x = makeTD $ fmap2 pB $ pT x

beginsWith x y = head x == y

pT = partition (`beginsWith` "s") 

pB  = partition (`beginsWith` "b") 

makeTD (k,(x,y)) = (pred $ ithWord 3 k' ,getBag x, (getVertices k', getEdges y )) where k' = head k

pG = partition (`beginsWith` "p")
rG (v,e) = (getVertices $ head v, getEdges e)

ithWord i xs= readInt $ xs !! i

getVertices xs = [1..k] where k = ithWord 2 xs
getEdges = map (\(x:y:[]) -> (readInt x,readInt y))

getBag :: File -> Bags
getBag y = Map.fromList $ map (\(b:x:xs) -> (readInt x, readInts xs)) y

type File = [[String]]
removeComments :: File -> File
removeComments [] = []
removeComments (x:xs) | head x == "c" = removeComments xs
                      | otherwise = x : (removeComments xs)


readGraph f = do 
	grp <- readFile f
	pure $ parseGraph . removeComments . map words . lines $ grp
	
readTreeD f = do 
	trd <- readFile f
	pure $ parseTDcmp . removeComments . map words . lines $ trd
	
	
	
