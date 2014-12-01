module FiniteComplete where

open import Agda.Primitive

infix 5 _->>_  _~>_ _=~=_

-- graph-like structure
_->>_ : {a b : Level} -> Set a -> Set b -> Set (a ⊔ b)
node ->> edge = node -> node -> edge

mutual

  --
  -- `Ob` - objects of the category
  --
  data Ob : Set where

    -- terminal object
    TerminalOb : 
      Ob

    -- cartesian product of objects
    _ProductOb_ : 
      (l r : Ob) ->
      Ob

    -- equalizer object
    _EqualizerOb_ : 
      {a b : Ob} ->
      (f g : a ~> b) ->
      Ob


  --
  -- `~>` - morphisms between objects
  --
  data _~>_ : Ob ->> Set where

    -- identity morphism
    IdMor : 
      (o : Ob) ->
      (o ~> o)

    -- composition of morphisms
    _MulMor_ : 
      {a b c : Ob} ->
      (a ~> b) -> (b ~> c) ->
      (a ~> c)
      
    -- morphism to terminal object
    TerminalMor : 
      (o : Ob) ->
      (o ~> TerminalOb)

    -- cartesian product is functor
    _ProductMor_ : 
      {l l' r r' : Ob} ->
      (l ~> l') -> (r ~> r') ->
      (l ProductOb r) ~> (l' ProductOb r')

    -- left projection of product
    _ProjectLeftMor_ : 
      (l r : Ob) ->
      (l ProductOb r) ~> l

    -- right projection of product
    _ProjectRightMor_ : 
      (l r : Ob) ->
      (l ProductOb r) ~> r

    -- diagonal morphism of product
    DiagonalMor : 
      (o : Ob) ->
      o ~> (o ProductOb o)

    -- equalizer is functor
    _EqualizerMor_ : 
      {a a' b b' : Ob} ->
      {f g : a ~> b} -> {f' g' : a' ~> b'} ->
      {ma : a ~> a'} -> {mb : b ~> b'} ->
      (ma MulMor f') =~= (f MulMor mb) ->  -- !
      (ma MulMor g') =~= (g MulMor mb) ->  -- !
      (f EqualizerOb g) ~> (f' EqualizerOb g')


  --
  -- `=~=` - equivalences between morphisms (2-morphisms)
  --
  data _=~=_ : {a b : Ob} -> (a ~> b) ->> Set where

    -- identity equivalence (reflectivity)
    IdEqu : 
      {a b : Ob} -> 
      (f : a ~> b) ->
      (f =~= f)

    -- composition of equivalences (transitivity)
    _MulEqu_ : 
      {a b : Ob} ->
      {f g h : a ~> b} ->
      (f =~= g) -> (g =~= h) ->
      (f =~= h)

    -- inverse equivalence (symmetry)
    InvEqu : 
      {a b : Ob} ->
      {f g : a ~> b} ->
      (f =~= g) -> 
      (g =~= f)

    -- multiplication of morphisms is congruence
    MulMorEqu : 
      {a b c : Ob} ->
      {f f' : a ~> b} -> {g g' : b ~> c} ->
      (f =~= f') -> (g =~= g') ->
      (f MulMor g) =~= (f' MulMor g')

    -- identity morphism is left neutral
    IdMorLeftNeutrEqu : 
      {a b : Ob} ->
      (f : a ~> b) ->
      ((IdMor a) MulMor f) =~= f

    -- identity morphism is right neutral
    IdMorRightNeutrEqu : 
      {a b : Ob} ->
      (f : a ~> b) ->
      (f MulMor (IdMor b)) =~= f

    -- composition of morphisms is associative
    MulMorAssocEqu : 
      {a b c d : Ob} ->
      (f : a ~> b) -> (g : b ~> c) -> (h : c ~> d) ->
      ((f MulMor g) MulMor h) =~= (f MulMor (g MulMor h))

    -- terminal morphism is natural
    TerminalMorNatEqu : 
      {a b : Ob} ->
      (f : a ~> b) ->
      TerminalMor a =~= (f MulMor (TerminalMor b))

    -- terminal morphism is unique (triangle equality of adjunction)
    TerminalTriangleEqu : 
      TerminalMor TerminalOb =~= IdMor TerminalOb

    -- cartesian product acts as congruence
    ProductEqu : 
      {l l' r r' : Ob} ->
      {ml ml' : l ~> l'} -> (mr mr' : r ~> r') ->
      (ml =~= ml') -> (mr =~= mr') ->
      (ml ProductMor mr) =~= (ml' ProductMor mr')

    -- product is functorial on identities
    _ProductIdEqu_ : 
      (l r : Ob) ->
      ((IdMor l) ProductMor (IdMor r)) =~= 
       (IdMor (l ProductOb r))

    -- product is functorial on composition
    ProductMulEqu : 
      {la lb lc ra rb rc : Ob} ->
      (lf : la ~> lb) -> (lg : lb ~> lc) -> (rf : ra ~> rb) -> (rg : rb ~> rc) ->
      ((lf MulMor lg) ProductMor (rf MulMor rg)) =~=
      ((lf ProductMor rf) MulMor (lg ProductMor rg))

    -- left projection of product is natural
    ProjectLeftMorNatEqu : 
      {l r l' r' : Ob} -> 
      (ml : l ~> l') -> (mr : r ~> r') ->
      ((l ProjectLeftMor r) MulMor ml) =~=
      ((ml ProductMor mr) MulMor (l' ProjectLeftMor r'))

    -- right projection of product is natural
    ProjectRightMorNatEqu : 
      {l r l' r' : Ob} -> 
      (ml : l ~> l') -> (mr : r ~> r') ->
      ((l ProjectRightMor r) MulMor mr) =~=
      ((ml ProductMor mr) MulMor (l' ProjectRightMor r'))

    -- diagonal of product is natural
    DiagonalMorNatEqu : 
      {a b : Ob} ->
      (f : a ~> b) ->
      ((DiagonalMor a) MulMor (f ProductMor f)) =~=
      (f MulMor (DiagonalMor b))

    -- 1st triangle of product adjunction
    ProductTriangleEqu : 
      (l r : Ob) ->
      ((DiagonalMor (l ProductOb r)) MulMor
        ((l ProjectLeftMor r) ProductMor (l ProjectRightMor r))) 
      =~= (IdMor (l ProductOb r))

    -- 2nd triangle of product adjunction
    ProductTriangleLeftEqu : 
      (o : Ob) ->
      ((DiagonalMor o) MulMor (o ProjectLeftMor o)) =~= (IdMor o)

    -- 2nd triangle of product adjunction
    ProductTriangleRightEqu : 
      (o : Ob) ->
      ((DiagonalMor o) MulMor (o ProjectRightMor o)) =~= (IdMor o)

    -- equalizer acts as congruence
    EqualizerEqu : 
      {a a' b b' : Ob} ->
      {f g : a ~> b} -> {f' g' : a' ~> b'} ->
      {ma ma' : a ~> a'} -> {mb mb' : b ~> b'} ->
      {ef : (ma MulMor f') =~= (f MulMor mb)} ->
      {ef' : (ma' MulMor f') =~= (f MulMor mb')} ->
      {eg : (ma MulMor g') =~= (g MulMor mb)} ->
      {eg' : (ma' MulMor g') =~= (g MulMor mb')} ->
      (ea : ma =~= ma') -> (eb : mb =~= mb') -> 
      (ef EqualizerMor eg) =~= (ef' EqualizerMor eg')

    -- equalizer is functorial on identities
    _EqualizerIdEqu_ : 
      {a b : Ob} ->
      (f g : a ~> b) -> 
      (((IdMorLeftNeutrEqu f) MulEqu (InvEqu (IdMorRightNeutrEqu f))) EqualizerMor 
       ((IdMorLeftNeutrEqu g) MulEqu (InvEqu (IdMorRightNeutrEqu g)))) 
        =~= IdMor (f EqualizerOb g)

    EqualizerMulEqu : 
      {a a' a'' b b' b'' : Ob} ->
      {f g : a ~> b} -> {f' g' : a' ~> b'} -> {f'' g'' : a'' ~> b''} ->
      {ma : a ~> a'} -> {mb : b ~> b'} ->
      {ma' : a' ~> a''} -> {mb' : b' ~> b''} ->
      (ef : (ma MulMor f') =~= (f MulMor mb)) ->
      (eg : (ma MulMor g') =~= (g MulMor mb)) ->
      (ef' : (ma' MulMor f'') =~= (f' MulMor mb')) ->
      (eg' : (ma' MulMor g'') =~= (g' MulMor mb')) ->
      (ef EqualizerMor eg) : (f EqualizerOb g) ~> (f' EqualizerOb g')
      MulMor 
      (ef EqualizerMor eg) : (f' EqualizerOb g') ~> (f'' EqualizerOb g'')
      =~=
