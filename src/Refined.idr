module Refined

import Data.List
import Props.Util
import Props.Char
import Props.String

%access public export
Refined : (a : Type) -> (P : a -> Type) -> Type
Refined = DPair

implicit 
toRefined : { a : Type } -> { P : a -> Type } -> (x:a) -> { auto property : P x } -> Refined a P
toRefined value {property} = (value ** property)

-- Havent yet figured out how to make Idris use an implicit generic fromRefined 
implicit 
fromCharRefined : { P : Char -> Type } -> Refined Char P -> Char
fromCharRefined = fst 

implicit
fromStringRefined : { P : String -> Type } -> Refined String P -> String
fromStringRefined = fst

x : Refined Char Digit
x = '0'

y : Refined Char Letter
y = 'A'

z : Refined Char LetterOrDigit
z = '0'

s : Refined String NonEmpty
s = "s"

test : Char -> IO ()
test c = printLn $ show c

main : IO ()
main = test Refined.x
