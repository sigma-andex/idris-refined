module Refined.Props.Util

import Data.List

%access public export

private
mkNo : {xs' : List a} ->
       ((x' = y') -> Void) ->
       (Elem x' xs' -> Void) ->
       Elem x' (y' :: xs') -> Void
mkNo f g Here = f Refl
mkNo f g (There x) = g x

-- Use this until https://github.com/idris-lang/Idris-dev/issues/4161
fastIsElem : DecEq a => (x : a) -> (xs : List a) -> Dec (Elem x xs)
fastIsElem x [] = No absurd
fastIsElem x (y :: xs) with (decEq x y)
  fastIsElem x (x :: xs) | (Yes Refl) = Yes Here
  fastIsElem x (y :: xs) | (No contra) with (fastIsElem x xs)
    fastIsElem x (y :: xs) | (No contra) | (Yes prf) = Yes (There prf)
    fastIsElem x (y :: xs) | (No contra) | (No f) = No (mkNo contra f)

using (a: Type, P : a -> Type, Q: a -> Type)

  data EitherK : { a : Type } -> ( P : a -> Type ) -> ( Q : a -> Type) -> a -> Type where
    LeftK : ( prf : P c ) -> EitherK P Q c
    RightK : ( prf : Q c ) -> EitherK P Q c

-- Add these to not depend on contrib
data Given : Dec x -> Type where
  Always : Given (Yes prf)

data Denied : Dec x -> Type where
  Never : Denied (No contra)
