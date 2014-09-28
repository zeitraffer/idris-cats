-- 
-- NNO.idr:
-- defines a finitely complete category 
-- with the free monad over identity functor
-- (equvivalent to presence of natural number object )
--

module NNO_Naive

{-
  Parts of the structure:

# basic: Morphism is a category
# basic: Equality is a groupoid
# limit: terminal object
# limit: cartesian product
# limit: equalizer
# recursion: free monad 
-}

Graph : Type -> Type
Graph t = (source, target: t) -> Type

mutual


  -------------------------------------------------------------
  ||| Object - objects of the main category

  data Object : Type 
    where
  {
    -- # limit: terminal object
    TerminalObject : 
      Object

    -- # limit: cartesian product
    ProductObject : 
      (oL, oR : Object) -> 
      Object

    -- # limit: equalizer
    EqulizerObject : 
      {o, o' : Object} ->
      (m, n : Morphism o o') ->
      Object

  }

  -------------------------------------------------------------
  ||| Morphism - morphisms between objects

  data Morphism : Graph Object
    where
  {
    -- # basic: Morphism is a category
    IdentityMorphism :       
      (o : Object) -> 
      Morphism o o

    -- # basic: Morphism is a category
    MultiplyMorphism : 
      {a, b, c : Object} -> 
      (m : Morphism a b) -> (n : Morphism b c) -> 
      Morphism a c

    -- # limit: terminal object
    TerminalUnit : 
      (o : Object) ->
      Morphism o TerminalObject

    -- # limit: cartesian product
    ProductMorphism : 
      {oL, oL', oR, oR' : Object} ->
      (mL : Morphism oL oL') -> (mR : Morphism oR oR') ->
      Morphism (ProductObject oL oR) (ProductObject oL' oR')

    -- # limit: cartesian product
    ProductUnit : 
      (o : Object) ->
      Morphism o (ProductObject o o)

    -- # limit: cartesian product
    ProductCounitLeft : 
      (oL, oR : Object) ->
      Morphism (ProductObject oL oR) oL

    -- # limit: cartesian product
    ProductCounitRight : 
      (oL, oR : Object) ->
      Morphism (ProductObject oL oR) oR
    
  }

  -------------------------------------------------------------
  ||| Equality - equalities between morphisms

  data Equality : Graph (Morphism o o')
    where
  {
    -- # basic: Equality is a groupoid
    InverseEquality : 
      {o, o' : Object} ->
      {m, m' : Morphism o o'} ->
      Equality m m' ->
      Equality m' m

    -- # basic: Equality is a groupoid
    IdentityEquality : 
      {o, o' : Object} -> 
      (m : Morphism o o') -> 
      Equality m m

    -- # basic: Equality is a groupoid
    MultiplyEquality : 
      {o, o' : Object} -> 
      {m, n, k : Morphism o o'} -> 
      (e : Equality m n) -> (f : Equality n k) -> 
      Equality m k

    -- # basic: Morphism is a category
    MultiplyMorphismEquality : 
      {a, b, c : Object} -> 
      {m, m' : Morphism a b} -> {n, n' : Morphism b c} ->
      (e : Equality m m') -> (f : Equality n n') ->
      Equality (MultiplyMorphism m n) (MultiplyMorphism m' n')

    -- # limit: terminal object
    TerminalUnitNaturality : 
      {o, o' : Object} ->
      (m : Morphism o o') ->
      Equality (TerminalUnit o) (MultiplyMorphism m (TerminalUnit o'))

    -- # limit: terminal object
    TerminalTriangle : 
      Equality (TerminalUnit TerminalObject) (IdentityMorphism TerminalObject)

    -- # limit: cartesian product
    ProductEquality : 
      {oL, oL', oR, oR' : Object} ->
      (mL, mL' : Morphism oL oL') -> (mR, mR' : Morphism oR oR') ->
      (eL : Equality mL mL') -> (eR : Equality mR mR') ->
      Equality (ProductMorphism mL mR) (ProductMorphism mL' mR')

    -- # limit: cartesian product
    ProductUnitNaturality : 
      {o, o' : Object} ->
      (m : Morphism o o') ->
      Equality (MultiplyMorphism (ProductUnit o) (ProductMorphism m m)) 
               (MultiplyMorphism m (ProductUnit o'))

    -- # limit: cartesian product
    ProductCounitLeftNaturality : 
      {oL, oR, oL', oR' : Object} -> 
      (mL : Morphism oL oL') -> (mR : Morphism oR oR') ->
      Equality (MultiplyMorphism (ProductCounitLeft oL oR) mL) 
               (MultiplyMorphism (ProductMorphism mL mR) 
                                 (ProductCounitLeft oL' oR'))

    -- # limit: cartesian product
    ProductCounitRightNaturality : 
      {oL, oR, oL', oR' : Object} ->
      (mL : Morphism oL oL') -> (mR : Morphism oR oR') ->
      Equality (MultiplyMorphism (ProductCounitRight oL oR) mR) 
               (MultiplyMorphism (ProductMorphism mL mR) 
                                 (ProductCounitRight oL' oR'))

    -- # limit: cartesian product
    ProductTriangle : 
      (oL, oR : Object) ->
      Equality (MultiplyMorphism (ProductUnit (ProductObject oL oR)) 
                                 (ProductMorphism (ProductCounitLeft oL oR) (ProductCounitRight oL oR))) 
               (IdentityMorphism (ProductObject oL oR))

    -- # limit: cartesian product
    ProductTriangleLeft : 
      (o : Object) ->
      Equality (MultiplyMorphism (ProductUnit o) 
                                 (ProductCounitLeft o o))
               (IdentityMorphism o)

    -- # limit: cartesian product
    ProductTriangleRight : 
      (o : Object) ->
      Equality (MultiplyMorphism (ProductUnit o)
                                 (ProductCounitRight o o))
               (IdentityMorphism o)

  }


