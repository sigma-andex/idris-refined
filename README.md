Idris-refined
====================

Port of [scala refined](https://github.com/fthomas/refined) library to idris using Sigma types.

# Examples

## Chars

Chars can be refined using the Refined type.
```idris
-- Only digits
x : Refined Char Digit
x = '0'

-- Only letters
y : Refined Char Letter
y = 'A'

-- Letters or Digits
z : Refined Char LetterOrDigit
z = '0'
```

Refined types can be passed to functions expecting ordinary types. 
```idris
test : Char -> IO ()
test c = print $ show c

main : IO ()
main = test Refined.x
```
