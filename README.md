Idris-refined 
====================
Port of [scala refined](https://github.com/fthomas/refined) library to idris using dependent pairs.

# Installation
```bash
git clone git@github.com:janschultecom/idris-refined.git
make install
idris -p Refined
Idris> :module Refined
```

# Example

Types can be refined using ```Refined```:

```idris
-- Only digits
zeroIsDigit : Refined Char Digit
zeroIsDigit = '0'
-- zeroIsDigit = 'a' will result in compile-time error

-- Only letters
upperAIsLetter : Refined Char Letter
upperAIsLetter = 'A'
-- upperAIsLetter = '0' will result in compile-time error

-- Letters or Digits
lowerAIsAlpha : Refined Char AlphaNumeric
lowerAIsAlpha = 'a'

upperAIsAlpha : Refined Char AlphaNumeric
upperAIsAlpha = 'A'

zeroIsAlpha : Refined Char AlphaNumeric
zeroIsAlpha = '0'
-- z = '$' will result in compile-time error

```

Refined types can be passed to functions expecting ordinary types.
```idris
test : Char -> IO ()
test c = print $ show c

main : IO ()
main = test Refined.x
```
See the Test case for more examples. 

# Predicates

## Nat

* Greater n: checks if a ```Nat``` is strictly greater than n
* GreaterEqual n: checks if a ```Nat``` is greater or equal to n
* Less n: checks if a ```Nat``` is strictly less than n
* LessEqual n: checks if a ```Nat``` is less or equal to n

## Char

* Digit: checks if a ```Char``` is a digit
* Letter: checks if a ```Char``` is a letter
* AlphaNumeric: checks if a ```Char``` is a letter or digit
* LowerCase: checks if a ```Char``` is a lower case character
* UpperCase: checks if a ```Char``` is an upper case character
* Whitespace: checks if a ```Char``` is white space

## String

* NonEmpty : checks if a ```String``` has at least one character
