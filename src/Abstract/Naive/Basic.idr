-- 
-- defines a basic category structure 
--

module Abstract.Naive.Basic

{-
  Parts of the structure:

# basic: Morphism is a category
# basic: Equality is a groupoid
-}

mutual


  -------------------------------------------------------------
  ||| Object - objects of the main category

  data Object : Type 
    where
  {
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

  }

