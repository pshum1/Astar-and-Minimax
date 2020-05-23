module MP.MP4 where
import Prelude hiding (lines)
import Data.Maybe
import Data.Ord
import Data.List hiding (lines)
import Data.List.Split (chunksOf)
import Data.Tree
import Data.Map (Map, empty, fromList, findWithDefault, member, insertWith)
import System.Random
import System.Random.Shuffle
import Control.Monad.State
import System.IO
import System.Console.ANSI
import Control.Concurrent
import GHC.IO


-- Search functions
-- generalized, higher-order search
search :: (Eq a, Show a) => 
          (a -> Bool) 
          -> (a -> [a]) 
          -> ([a] -> [a] -> [a])
          -> [a] -> [a] 
          -> Maybe a
search goal adj comb unvisited visited
  | null unvisited = Nothing
  | goal (head unvisited) = Just (head unvisited)
  | otherwise = let (n:ns) = unvisited
                in debug n $ 
                  search goal adj comb
                    (comb (removeDups (adj n)) ns)
                    (n:visited)
  where removeDups = filter (not . (`elem` (unvisited ++ visited)))


debug :: Show a => a -> b -> b
debug x y = unsafePerformIO clearScreen `seq`
            unsafePerformIO (setCursorPosition 0 0) `seq`
            unsafePerformIO (putStrLn $ show x) `seq`
            unsafePerformIO (threadDelay $ 3*10^5) `seq`
            y


bestFirstSearch :: (Eq a, Show a, Ord b) => 
                   (a -> Bool) 
                   -> (a -> [a])
                   -> (a -> b) 
                   -> a -> Maybe a
bestFirstSearch goal succ cost start = search goal succ comb [start] []
  where comb new old = sortOn cost (new ++ old)

getRandom :: (Int, Int) -> State StdGen Int
getRandom range = do gen <- get
                     let (val, gen') = randomR range gen
                     put gen'
                     return val

getShuffled :: [a] -> State StdGen [a]
getShuffled l = do gen <- get
                   let (g1, g2) = split gen
                       l' = shuffle' l (length l) g1
                   put g2
                   return l'


-- Part 1: Pathfinding model

type Coordinate = (Double, Double) -- (x,y) coordinates of node

data Location = Loc { 
                  locName :: String,
                  locPos  :: Coordinate
                } deriving (Show, Eq)

distance :: Location -> Location -> Double
distance (Loc _ (x1,y1)) (Loc _ (x2,y2)) = sqrt $ (x1-x2)^2 + (y1-y2)^2

testLocs = [Loc "A" (0,0),
            Loc "B" (4,5),
            Loc "C" (3,10),
            Loc "D" (9, 15),
            Loc "E" (10, 20),
            Loc "F" (13, 25),
            Loc "G" (3, 6),
            Loc "H" (15, 30)]   

makeRandomList :: Int -> (Int, Int) -> [Double]
makeRandomList n r = replicate n $ fromIntegral(evalState (getRandom r) (mkStdGen 0))

-- genLocs produces locations with same coordinates
genLocs :: [String] -> (Int, Int) -> [Location]
genLocs n@(n1:ns) range = let nCoords = makeRandomList ((length n)*2) range
                          in createlocs n nCoords
    where createlocs [] _ = []
          createlocs (n':n'') (c:c':cc) = Loc n' (c,c') : createlocs n'' cc

within :: Double -> Location -> [Location] -> [Location]
within dist loc@(Loc name _) locs = [ l | l <- locs,
                                          distance loc l <= dist,
                                          locName l /= name]


data Path = Path { pathDist :: Double,
                   pathLocs :: [Location]
                 } deriving Eq


drawPath :: Path -> String
drawPath (Path _ []) = "Empty"
drawPath (Path pd ((Loc name pp):[])) = (show pp) ++ name ++ " | " ++  "Total Distance: " ++ show pd
drawPath p@(Path pd pl@((l@(Loc name pp)):plocs)) = ((show pp) ++ " " ++ name ++ " <- ") ++ drawPath (Path pd plocs) 

instance Show Path where
  show = drawPath

-- Makes a Path from a list of locations
makePath :: [Location] -> Path
makePath [] = Path 0 []
makePath l = Path (calcDistance l) l

-- Calculates the distance of a list of locations
calcDistance :: [Location] -> Double
calcDistance (Loc _ ploc : []) = 0
calcDistance l@(Loc _ ploc: locs) = distance (head l) (head locs) + calcDistance locs

-- Extends the paths given a distance
extendPath :: Double -> [Location] -> Path -> [Path]
extendPath dist locs p@(Path pd l) = let nextLocs = filter (not . (`elem` l)) $ within dist (head l) locs
                                     in newPath p nextLocs                       
    where newPath :: Path -> [Location] -> [Path]
          newPath p' [] = []
          newPath x@(Path pd l) (y:ys) = (makePath (y : l)) : (newPath x ys)

-- Extends the locations given a distance
extendPath' :: Double -> [Location] -> [Location] -> [[Location]]
extendPath' d locs p@(l@(Loc name (x,y)): _) = map (:p) nextLocs
    where nextLocs = filter (not . (`elem` p)) $ within d l locs

-- A star uses the distance remaining along with the distance so far
aStarSearch :: Double -> [Location] -> Location -> Location -> Maybe Path
aStarSearch range locs start end = do
    d <- bestFirstSearch goal succ cost [start]
    return $ makePath d
    where goal = (==end) . head
          succ = extendPath' range locs
          cost p = distance (head p) end + calcDistance p

-- A star prime uses the remaining
aStarSearch' :: Double -> [Location] -> Location -> Location -> Maybe [Location]
aStarSearch' range locs start end = bestFirstSearch goal succ cost [start]
    where goal = (==end) . head
          succ = extendPath' range locs
          cost p = distance (head p) end + fromIntegral (length p)

trySearch :: Maybe Path
trySearch = aStarSearch 10 testLocs (head testLocs) (last testLocs)

trySearch' :: Maybe [Location]
trySearch' = aStarSearch' 20 testLocs (head testLocs) (last testLocs)

-- Part 2: Modeling Nim and using MinMax

-- In this game there is a board with n number of pieces
-- Two players alternate turns and can take 1-3 pieces
-- The player that takes the last piece loses

data Board = Board { bTurn :: Turn,
                     bPieces :: [Int]
                   } deriving Eq

data Turn = P1 | P2 deriving (Eq, Show, Read)

drawBoard :: Board -> String
drawBoard (Board _ []) = "Finished"
drawBoard (Board t pieces@(p:ps)) = (show t) ++ " turn : " ++ (show pieces)

instance Show Board where
    show = drawBoard

opponent :: Turn -> Turn
opponent P1 = P2
opponent P2 = P1

startingBoard :: Int -> Board
startingBoard n = Board P1 $ replicate n 0

moves :: Board -> [Int]
moves (Board _ ps) = [n | n <- [1 .. length ps], n <= 3]

nim :: Int -> Board -> Board
nim n b@(Board t ps) = case n `elem` (moves b) of -- Checks to see if move is valid
                            True -> Board (opponent t) (drop n ps)
                            False -> Board t ps -- Illegal Move!

nims :: [Int] -> Board -> Board
nims move (Board t ps) = play move t $ Board t ps
    where play [] _ b = b
          play (m:ms) t b = play ms (opponent t) $ nim m b
          
won :: Board -> Bool
won (Board t p) = length p == 0

wins :: Turn -> Board -> Bool
wins player b@(Board t p) = case won b of
                                 True -> if (player == t) then True
                                         else False
                                 False -> False

-- Testing a board with a predetermined winner
testPlay :: Board
testPlay = nims [3,1,2,3] $ startingBoard 12


playInteractive :: Int -> IO ()
playInteractive n = play P1 $ startingBoard n
    where play turn board
            | wins P1 board = putStrLn "P1 Wins!"
            | wins P2 board = putStrLn "P2 Wins!"
            | otherwise = do
                putStr "Play a move (1-3): "
                move <- readLn
                case move `elem` (moves board) of
                     False -> do putStrLn "Illegal move"
                                 play turn board
                     True ->  do let board' = nim move $ board
                                 print board'
                                 play (opponent turn) board'


nextBoards :: Board -> [Board]
nextBoards b = map (flip nim b) (moves b)

gameTree :: Board -> Tree Board
gameTree b = Node b $ map gameTree $ nextBoards b

prune :: Int -> Tree a -> Tree a
prune 0 (Node x _) = Node x []
prune _ (Node x []) = Node x []
prune n (Node x ns) = Node x $ map (prune (n-1)) ns

printTree :: Board -> IO ()
printTree = putStrLn . drawTree . fmap show . gameTree


-- we need to figure out scores

data Scored a = Scored { score :: Int, scoredVal :: a}

instance Eq (Scored a) where
  (Scored x _) == (Scored y _) = x == y

instance Ord (Scored a) where
  compare (Scored x _) (Scored y _) = compare x y

instance Show a => Show (Scored a) where
  show (Scored s v) = "Score: " ++ show s ++ "\n\n" ++ show v


scoreBoard :: Turn -> Board -> Scored Board
scoreBoard t b | wins t b = Scored 100 b
               | wins (opponent t) b = Scored (-100) b
               | otherwise = Scored 0 b

-- we can see the nodes leading to min-max values
printScoredTree :: Board -> IO ()
printScoredTree = putStrLn . drawTree . fmap (show . scoreBoard P1) . gameTree

-- minimax algorithm
minimax :: (a -> Scored a) -> Tree a -> Scored a
minimax scorefn (Node _ ns) = maximize ns
  where maximize = maximumBy (comparing score) . map (eval minimize)
        minimize = minimumBy (comparing score) . map (eval maximize)
        eval _ (Node x []) = scorefn x
        eval f (Node x ns) = let Scored s _ = f ns in Scored s x

-- Enter a starting number of coins
playAI :: Int -> IO ()
playAI n = play P1 $ startingBoard n
    where play _ b  | wins P1 b = putStrLn "P1 wins!"
                    | wins P2 b = putStrLn "P2 wins!"
          play P1 b = do 
            putStr "Play a move: (1-3) "
            move <- readLn
            case move `elem` (moves b) of
                 False  -> do putStrLn "Illegal move"
                              play P1 b
                 True   -> do let board' = nim move $ b
                              print board'
                              play P2 board'
          play P2 b = do
            let b' = scoredVal $ minimax (scoreBoard P2) (gameTree b)
            print b'
            play P1 b'
  
            
aIplayAI :: Int -> IO ()
aIplayAI n = play P1 $ startingBoard n
    where play _ b  | wins P1 b = putStrLn "P1 wins!"
                    | wins P2 b = putStrLn "P2 wins!"
          play P1 b = do 
            let b' = scoredVal $ minimax (scoreBoard P1) (gameTree b)
            print b'
            play P2 b'
            
          play P2 b = do
            let b' = scoredVal $ minimax (scoreBoard P2) (gameTree b)
            print b'
            play P1 b'