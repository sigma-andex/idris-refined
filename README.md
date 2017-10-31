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
x : Refined Char Digit
x = '0'
-- x = 'a' will result in compile-time error

-- Only letters
y : Refined Char Letter
y = 'a'
-- y = '0' will result in compile-time error

-- Letters or Digits
z : Refined Char LetterOrDigit
z = '0'
-- z = '$' will result in compile-time error
```

Refined types can be passed to functions expecting ordinary types.
```idris
test : Char -> IO ()
test c = print $ show c

main : IO ()
main = test Refined.x
```

# Predicates

## Char

* Digit: checks if a ```Char``` is a digit
* Letter: checks if a ```Char``` is a letter
* LetterOrDigit: checks if a ```Char``` is a letter or digit
* LowerCase: checks if a ```Char``` is a lower case character
* UpperCase: checks if a ```Char``` is an upper case character
* Whitespace: checks if a ```Char``` is white space

## String

* NonEmpty : checks if a ```String``` has at least one character
