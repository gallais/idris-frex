||| Move these to stdlib Data.Vect.Extra
module Data.Vect.Extra

import Data.Vect
import Data.Fin
import Data.Vect.Elem

||| Version of `map` with runtime-irrelevant access to the current position
public export
mapWithPosIrrelevant : (f : (0 i : Fin n) -> a -> b) -> Vect n a -> Vect n b
mapWithPosIrrelevant f [] = []
mapWithPosIrrelevant f (x :: xs) = f 0 x :: mapWithPosIrrelevant (\i => f (FS i)) xs

||| Version of `map` with runtime-irrelevant information that the
||| argument is an element of the vector
public export
mapWithElem : (xs : Vect n a) -> (f : (x : a) -> (0 pos : x `Elem` xs) -> b) -> Vect n b
mapWithElem []        f = []
mapWithElem (x :: xs) f = f x Here :: mapWithElem xs (\x,pos => f x (There pos))
