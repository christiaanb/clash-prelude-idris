module Main

import CLaSH.Prelude

dotp : Num a => Vect n a -> Vect n a -> a
dotp as bs = foldr (+) 0 (zipWith (*) as bs)

fir : (Num a, Default a) => Vect (S (S n)) (Signal a) -> Signal a -> Signal a
fir {a} coeffs x_t = y_t
  where
    xs : Default a => Vect (S (S n)) (Signal a)
    xs  = window x_t
    y_t = dotp coeffs xs

topEntity : Signal Integer -> Signal Integer
topEntity = fir [2,3,-2,8]

testInput : List Integer
testInput = [2,3,-2,8]

expectedOutput : List Integer
expectedOutput = [4,12,1,20]

main : IO ()
main = putStrLn (show $ simulate topEntity testInput == expectedOutput)
