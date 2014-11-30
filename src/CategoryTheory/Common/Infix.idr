module CategoryTheory.Common.Infix

------------------------------------------------------------

%access public
%default total

------------------------------------------------------------

infixr 1 ~>, ~~>, :>, +>, *>, >- 
infixr 1 ->>, |+>|, |~>|, |:>|, |*>|
infixl 15 $, $:
infixl 9 #, &, >>>              

(->>) : Type -> Type -> Type
node ->> edge = (source, target: node) -> edge

