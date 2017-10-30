module Refined

import Data.List
import Props.Util
import Props.Char

%access public export
Refined : (a : Type) -> (P : a -> Type) -> Type
Refined = DPair

implicit 
toRefined : { a : Type } -> { P : a -> Type } -> (x:a) -> { auto property : P x } -> Refined a P
toRefined value {property} = (value ** property)

implicit 
fromCharRefined : { P : Char -> Type } -> Refined Char P -> Char
fromCharRefined = fst 

x : Refined Char Digit
x = '0'

y : Refined Char Letter
y = 'A'

z : Refined Char LetterOrDigit
z = '0'

test : Char -> IO ()
test c = printLn $ show c

main : IO ()
main = test Refined.x
