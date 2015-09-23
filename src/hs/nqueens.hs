import Smten.Prelude
import Smten.Control.Monad
import Smten.Symbolic
import Smten.Symbolic.Solver.MiniSat
import Smten.System.Environment

-- SMTEN Example

-- Placement: A list of locations (row, col) for each queen.
-- Indices go from 0 to n-1
type Placement = [(Int, Int)]

pretty :: Placement -> String
pretty places = unlines [[if (r, c) `elem` places then 'X' else '.'
                            | c <- [0..(length places - 1)]]
                            | r <- [0..(length places - 1)]]

distinct :: (Eq a) => [a] -> Bool
distinct [] = True
distinct (x:xs) = x `notElem` xs && distinct xs

islegal :: Placement -> Bool
islegal places = and [
  distinct (map fst places),
  distinct (map snd places),
  distinct (map (uncurry (+)) places),
  distinct (map (uncurry (-)) places)]

mkcol :: Int -> Symbolic Int
mkcol n = msum (map return [0..(n-1)])

nqueens :: Int -> IO ()
nqueens n = do
  result <- run_symbolic minisat $ do
              let rows = [0..(n-1)]
              cols <- sequence $ replicate n (mkcol n)
              let places = zip rows cols
              assert (islegal places)
              return places
  case result of
    Nothing -> putStrLn "no solution"
    Just v -> putStrLn (pretty v)

usage :: IO ()
usage = putStrLn "nqueens <n>"

main :: IO ()
main = do
  args <- getArgs
  case args of
     [x] -> nqueens (Smten.Prelude.read x)
     _ -> usage

