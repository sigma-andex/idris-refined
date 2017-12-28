module Props.Char

import Data.List
import public Props.Util

%access public export

digits : List Char
digits = ['0'..'9']

lowerCase : List Char
lowerCase = ['a'..'z']

upperCase : List Char
upperCase = ['A'..'Z']

letters : List Char
letters = lowerCase ++ upperCase

whiteSpace : List Char
whiteSpace = ['\n','\t',' ']

Digit : Char -> Type
Digit c = Elem c digits

LowerCase : Char -> Type
LowerCase c = Elem c lowerCase

UpperCase : Char -> Type
UpperCase c = Elem c upperCase

Whitespace : Char -> Type
Whitespace c = Elem c whiteSpace

Letter : (c:Char) -> Type
Letter = EitherK LowerCase UpperCase

AlphaNumeric : Char -> Type
AlphaNumeric = EitherK Letter Digit
