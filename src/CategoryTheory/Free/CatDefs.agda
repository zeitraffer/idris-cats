module CatDefs where

open import Agda.Primitive public

record CatRec : Set (lsuc lzero) where
  constructor MkCat
  field
    fOb : Set
    fMor : (a b : fOb) -> Set
    fEqu : (a b : fOb) -> (f g : fMor a b) -> Set
    fId : (a : fOb) -> fMor a a
    fMul : (a b c : fOb) -> fMor a b -> fMor b c -> fMor a c
open CatRec    

record CatOb (cat : CatRec) : Set where
  constructor MkOb
  field unOb : fOb cat
open CatOb

record _CatMor_ {cat : CatRec} (a b : CatOb cat) : Set where
  constructor MkMor
  field unMor : fMor cat (unOb a) (unOb b)
open _CatMor_

record _CatEqu_ {cat : CatRec} {a b : CatOb cat} (f g : a CatMor b) : Set where
  constructor MkEqu
  field umEqu : fEqu cat (unOb a) (unOb b) (unMor f) (unMor g)
open _CatEqu_

CatId : {cat : CatRec} -> (a : CatOb cat) -> a CatMor a
CatId {cat} a = MkMor (fId cat (unOb a))

_CatMul_ : {cat : CatRec} -> {a b c : CatOb cat} -> 
  a CatMor b -> b CatMor c -> a CatMor c
_CatMul_ {cat} {a} {b} {c} f g = 
  MkMor (fMul cat (unOb a) (unOb b) (unOb c) (unMor f) (unMor g))

-- test compatibility
WrapCat : CatRec -> CatRec
WrapCat cat = record {
    fOb = CatOb cat;
    fMor = _CatMor_;
    fEqu = \_ _ -> _CatEqu_;
    fId = CatId;
    fMul = \_ _ _ -> _CatMul_
  }

