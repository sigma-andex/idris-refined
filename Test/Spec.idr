module Test.Spec

import Refined

import Props.Util
import Props.Char
import Props.String
import Props.Nat 

%access public export

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

-- TODO: Proof these using Void
--dollarIsNotAlpha : Refined Char AlphaNumeric -> Void
--dollarIsNotAlpha = '$'

blankIsWhitespace : Refined Char Whitespace
blankIsWhitespace = ' '

textIsNonEmpty : Refined String NonEmpty
textIsNonEmpty = "text"

-- FIXME: Somehow implicit conversion doesnt work here
oneIsGreaterThanZero : Refined Nat (Greater Z)
oneIsGreaterThanZero = toRefined $ S Z 

--zeroIsGreaterThanZero : Refined Nat (Greater Z)
--zeroIsGreaterThanZero = toRefined $ Z 

oneIsGreaterEqualOne : Refined Nat $ GreaterEqual $ S Z 
oneIsGreaterEqualOne = toRefined $ S Z 

zeroIsLessThanOne : Refined Nat (Less (S Z))
zeroIsLessThanOne = toRefined Z 

--zeroIsLessThanZero : Refined Nat (Less Z)
--zeroIsLessThanZero = toRefined Z 

testMe : IO()
testMe = putStrLn("Passed")
