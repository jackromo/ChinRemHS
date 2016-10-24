import Data.List
import Data.Maybe


gcdnew :: Int -> Int -> Int
gcdnew a 0 = a
gcdnew a b = gcdnew b (a `mod` b)


euclid_internal :: (Int, Int) -> (Int, Int) -> (Int, Int) -> (Int, Int)
euclid_internal (a, b) (s_old, t_old) (s, t)
  | a `mod` b == 0 = (s, t)
  | otherwise =
    let s_old2 = s
        t_old2 = t
        s2 = s_old - (a `div` b) * s
        t2 = t_old - (a `div` b) * t
    in euclid_internal (b, a `mod` b) (s_old2, t_old2) (s2, t2)


euclid :: Int -> Int -> (Int, Int)
euclid a b = euclid_internal (a, b) (1, 0) (0, 1)


-- Modulus relationship
data Modrel = Modrel { coeff :: Int, congTo :: Int, modulo :: Int}
            deriving (Show, Eq)


congHasSoln :: Modrel -> Bool
congHasSoln (Modrel a b n) = (b `mod` gcdnew a n) == 0


congSimplify :: Modrel -> Modrel
congSimplify (Modrel a b n) =
  let gcd_ = gcdnew a n
  in Modrel (a `div` gcd_) (b `div` gcd_) (n `div` gcd_)


-- if a'x = b' mod n', then xa' + tn' = b'
-- gcd(a', n') = 0 => x = b'x' and t = b't'
-- then just do euclid's algorithm to find t' and x'
-- x will be x'b'
-- (NB: this only gives one solution obviously)
congFirstSoln :: Modrel -> Maybe Int
congFirstSoln (Modrel a b n)
  | not$ congHasSoln (Modrel a b n) = Nothing
  | otherwise =
    let (x', _) = euclid a n
        b' = b `div` (gcdnew a n)
    in Just (b' * x')


-- gives i'th congruence solution, eg. 0th, -1st, 4th, etc.
congIthSoln :: Modrel -> Int -> Maybe Int
congIthSoln (Modrel a b n) i =
  let multiplicand = n `div` (gcdnew a n)
      firstSoln = congFirstSoln (Modrel a b n)
  in case firstSoln of
     Just soln -> Just ((i * multiplicand) + soln)
     Nothing -> Nothing


-- gives number of values in a list a value divides
-- used to determine if a list of values are coprime
numIntsValDivides :: [Int] -> Int -> Int
numIntsValDivides [x] val = if x `mod` val == 0 then 1 else 0
numIntsValDivides [] val = 0
numIntsValDivides (x:xs) val
  | x `mod` val == 0 = 1 + numIntsValDivides xs val
  | otherwise = numIntsValDivides xs val


-- states whether a list of integers are all coprime
intsCoprime :: [Int] -> Bool
intsCoprime [x] = True
intsCoprime xs =
  let divideCounts = map (numIntsValDivides xs) [2..(maximum xs)]
  in 1 >= maximum divideCounts


-- check whether a list of mod relations have solutions
modrelsHaveSolns :: [Modrel] -> Bool
modrelsHaveSolns [] = False
modrelsHaveSolns mods = 0 == (length $ filter ((not) . (congHasSoln)) mods)


-- takes a list of modrels and shows if they have one solution.
-- ie. if they are all coprime and each one is solvable, as well as all having coeff of 1
chinRemHasOneSoln :: [Modrel] -> Bool
chinRemHasOneSoln [] = False
chinRemHasOneSoln mods
  | (find (\n -> 1 /= (coeff n)) mods) /= Nothing = False
  | modrelsHaveSolns mods = intsCoprime $ map (modulo) mods
  | otherwise = False


-- make modrels used by chinese remainder soln for a^i
chinRemGetModRels :: [Modrel] -> [Modrel]
chinRemGetModRels [] = []
chinRemGetModRels mods =
  let modProd = foldr (*) 1 $ map (modulo) mods
  in map (\m -> Modrel (modProd `div` (modulo m)) 1 (modulo m)) mods


-- get coeff for collective congruence from many congruences
chinRemGetCoeff :: [Modrel] -> Int
chinRemGetCoeff [] = 0
chinRemGetCoeff mods =
  let newMods = chinRemGetModRels mods
  in let congs = map (congTo) mods
         aCoeffs = map (coeff) newMods
         xCoeffs = map ((fromJust) . (congFirstSoln)) newMods
     in foldr (+) 0 $ map (\i -> (congs!!i) * (aCoeffs!!i) * (xCoeffs!!i)) [0..((length mods) - 1)]


-- get common congruence from modrels with coprime moduli.
-- x = (c1a1x1 + c2a2x2 + ... + ckakxk) mod n1n2n3...nk
-- where aixi = 1 mod ni
chinRemModRel :: [Modrel] -> Maybe Modrel
chinRemModRel mods
  | chinRemHasOneSoln mods =
    let newModulo = foldr (*) 1 $ map (modulo) mods
    in Just (Modrel 1 (chinRemGetCoeff mods) newModulo)
  | otherwise = Nothing

