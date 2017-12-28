module Test.Spec

import Refined

import Props.Util
import Props.Char
import Props.String

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

--dollarIsNotAlpha : Refined Char AlphaNumeric -> Void
--dollarIsNotAlpha = '$'

blankIsWhitespace : Refined Char Whitespace
blankIsWhitespace = ' '

textIsNonEmpty : Refined String NonEmpty
textIsNonEmpty = "text"

test : Char -> IO ()
test c = printLn $ show c

testMe : IO()
testMe = putStrLn("Passed")
