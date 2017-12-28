module Refined

import Data.List

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

implicit
fromNatRefined : { P : Nat -> Type } -> Refined Nat P -> Nat
fromNatRefined = fst

