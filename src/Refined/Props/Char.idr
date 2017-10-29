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

using (a: Type, P : a -> Type, Q : a -> Type)  
  data DecCoProduct : (c:a) -> (left : Dec (P c)) -> (right : Dec (Q c)) -> Type where 
    InL : DecCoProduct c (Yes x) (No y) 
    InR : DecCoProduct c (No x) (Yes y) 
 
  Or : ( f : (x:a) -> Dec (P x) ) -> 
       ( g : (x:a) -> Dec (Q x) ) -> 
       ( c : a) -> 
       Type 
  Or f g c = DecCoProduct c (f c) (g c)

Letter : Char -> Type
Letter = Or (\c => fastIsElem c Refined.Props.lowerCase) (\c => fastIsElem c Refined.Props.upperCase)

