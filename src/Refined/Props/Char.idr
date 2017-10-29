module Refined.Props

import Data.List
import Data.List.Quantifiers

%access public export

digits : List Char
digits = ['0'..'9']

lowerCase : List Char
lowerCase = ['a'..'z']

upperCase : List Char
upperCase = ['A'..'Z']

Digit : Char -> Type
Digit = \c => Elem c Refined.Props.digits

LowerCase : Char -> Type
LowerCase = \c => Elem c Refined.Props.lowerCase

UpperCase : Char -> Type
UpperCase = \c => Elem c Refined.Props.upperCase

mkNo : {xs' : List a} ->
       ((x' = y') -> Void) -> 
       (Elem x' xs' -> Void) ->
       Elem x' (y' :: xs') -> Void
mkNo f g Here = f Refl
mkNo f g (There x) = g x

fastIsElem : DecEq a => (x : a) -> (xs : List a) -> Dec (Elem x xs)
fastIsElem x [] = No absurd
fastIsElem x (y :: xs) with (decEq x y)
  fastIsElem x (x :: xs) | (Yes Refl) = Yes Here
  fastIsElem x (y :: xs) | (No contra) with (fastIsElem x xs)
    fastIsElem x (y :: xs) | (No contra) | (Yes prf) = Yes (There prf)
    fastIsElem x (y :: xs) | (No contra) | (No f) = No (mkNo contra f)

--using (a : Type, P : a -> Type, Q : a -> Type) 

--  data Or : (c:a) -> (left : Dec x) -> (right : Dec y) -> Type where 
--    InL : Or c (Yes x) (No y) 
--    InR : Or c (No x) (Yes y) 

data OrX : (c:a) -> (left : Dec x) -> (right : Dec y) -> Type where 
  InL : OrX c (Yes x) (No y) 
  InR : OrX c (No x) (Yes y) 
  
Or : (c:a) -> 
     { P : a -> Type } -> 
     (left : a -> Dec (P c)) -> 
     { Q : a -> Type } -> 
     (right : a -> Dec (Q c)) -> 
     Type
Or c left right = OrX c (left c) (right c)

X : (c:Char) -> Dec (Elem c Refined.Props.lowerCase)
X c = fastIsElem c Refined.Props.lowerCase

Y : (c:Char) -> Dec (Elem c Refined.Props.lowerCase)
Y c = fastIsElem c Refined.Props.upperCase

x : Or 'A' X Y 
x = ?h

-- isElem : DecEq a => (x : a) -> (xs : List a) -> Dec (Elem x xs)
-- any : {P : a -> Type} -> (dec : (x : a) -> Dec (P x)) -> (xs : List a) -> Dec (Any P xs)
isLowerCase : (c:Char) -> Dec (Elem c Refined.Props.lowerCase)
isLowerCase c = isElem c Refined.Props.lowerCase
