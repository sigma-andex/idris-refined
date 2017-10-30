module Refined.Props.Char

import Data.List
import Data.List.Quantifiers
import Props.Util

%access public export

digits : List Char
digits = ['0'..'9']

lowerCase : List Char
lowerCase = ['a'..'z']

upperCase : List Char
upperCase = ['A'..'Z']

letters : List Char
letters = lowerCase ++ upperCase

Digit : Char -> Type
Digit = \c => Elem c digits

LowerCase : Char -> Type
LowerCase = \c => Elem c lowerCase

UpperCase : Char -> Type
UpperCase = \c => Elem c upperCase

Whitespace : Char -> Type
Whitespace = (=) "" 

Letter : (c:Char) -> Type 
Letter = Or (\c => fastIsElem c lowerCase) (\c => fastIsElem c upperCase)

isDigit : (c:Char) -> Dec (Elem c Refined.Props.Char.digits)
isDigit = \c => fastIsElem c digits

isLetter : (c:Char) -> Dec (Elem c Refined.Props.Char.letters)
isLetter = \c => fastIsElem c letters 

LetterOrDigit : Char -> Type
--LetterOrDigit = Or (\c => Dec (Letter c)) (\c => Dec (Digit c)) 
LetterOrDigit = Or isLetter isDigit 

