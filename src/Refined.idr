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

zeroIsDigit : Refined Char Digit
zeroIsDigit = '0'

upperAIsLetter : Refined Char Letter
upperAIsLetter = 'A'

lowerAIsAlpha : Refined Char AlphaNumeric
lowerAIsAlpha = 'a'

upperAIsAlpha : Refined Char AlphaNumeric
upperAIsAlpha = 'A'

zeroIsAlpha : Refined Char AlphaNumeric
zeroIsAlpha = '0'

--dollarIsNotAlpha : Refined Char AlphaNumeric -> Void 
--dollarIsNotAlpha = absurd $ toRefined '$'

blankIsWhitespace : Refined Char Whitespace
blankIsWhitespace = ' '

textIsNonEmpty : Refined String NonEmpty
textIsNonEmpty = "text"

test : Char -> IO ()
test c = printLn $ show c

main : IO ()
main = test Refined.upperAIsAlpha
