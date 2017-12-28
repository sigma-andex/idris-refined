module Props.Nat

import Props.Util

%access public export

Greater : Nat -> Nat -> Type
--Greater n m = GT m n
Greater = flip GT

GreaterEqual : Nat -> Nat -> Type
GreaterEqual = flip GTE

Less : Nat -> Nat -> Type
Less = flip LT

LessEqual : Nat -> Nat -> Type
LessEqual = flip LTE
