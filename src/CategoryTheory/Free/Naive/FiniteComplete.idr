module CategoryTheory.Free.Naive.FiniteComplete

--import Structs.CatDefs

--infixl 5 `MulEqu` `MulMor`

mutual

  private syntax Term tag = / tag /

  --
  -- internal types of terms
  --
  data Tag 
      {level : Level} 
      (cat : CatRec level) : 
      Set level
    where

      -- objects
      Ob : 
        Tag cat

      -- morphisms between objects
      _Mor_ : 
        (sourceOb targetOb : / Ob {cat = cat}/) -> 
        Tag cat

      -- equalities between morphisms
      _Equ_ : 
        {sourceOb targetOb : / Ob {cat = cat}/} -> 
        (sourceMor targetMor : / sourceOb Mor targetOb /) ->
        Tag cat

      -- XXX to remove
      Square : 
        {a a' b b' : / Ob {cat = cat}/} -> 
        (f : / a Mor b /) -> 
        (f' : / a' Mor b' /) ->
        (ma : / a Mor a' /) -> 
        (mb : / b Mor b' /) ->
        Tag cat

  --
  -- terms of internal types
  --
  data Term
      {level : Level} 
      {cat : CatRec level} : 
      Tag cat ->
      Set level
    where
      
      --=======================================================
      -- category structure
      --=======================================================

      -- identity morphism 
      IdMor : 

        (o : / Ob /) ->
        ---------------
        / o Mor o /

      -- composition of morphisms 
      _MulMor_ : 

        {a b c : / Ob /} ->
        / a Mor b / -> 
        / b Mor c / ->
        -------------------------
        / a Mor c /

      -- identity equivalence (reflectivity)
      IdEqu : 

        {a b : / Ob /} -> 
        (f : / a Mor b /) ->
        ----------------
        / f Equ f /

      -- composition of equivalences (transitivity)
      _MulEqu_ : 

        {a b : / Ob /} ->
        {f g h : / a Mor b /} ->
        / f Equ g / -> 
        / g Equ h / ->
        --------------------
        / f Equ h /

      -- inverse equivalence (symmetry) 
      InvEqu : 

        {a b : / Ob /} ->
        {f g : / a Mor b /} ->
        / f Equ g / -> 
        ------------------
        / g Equ f /

      -- multiplication of morphisms is congruence 
      _MulMorEqu_ : 

        {a b c : / Ob /} ->
        {f f' : / a Mor b /} -> 
        {g g' : / b Mor c /} ->
        / f Equ f' / -> 
        / g Equ g' / ->
        -----------------------------------
        /(f MulMor g) Equ (f' MulMor g')/

      -- identity morphism is left neutral 
      IdMorLeftNeutrEqu : 

        {a b : / Ob /} ->
        (f : / a Mor b /) ->
        ------------------------------
        /((IdMor a) MulMor f) Equ f /

      -- identity morphism is right neutral 
      IdMorRightNeutrEqu : 

        {a b : / Ob /} ->
        (f : / a Mor b /) ->
        ------------------------------
        /(f MulMor (IdMor b)) Equ f /

      -- composition of morphisms is associative 
      MulMorAssocEqu : 

        {a b c d : / Ob /} -> 
        {f : / a Mor b /} -> 
        {g : / b Mor c /} -> 
        {h : / c Mor d /} -> 
        -----------------------------
        / (f MulMor (g MulMor h))
            Equ 
          ((f MulMor g) MulMor h) /
      
      --=======================================================
      -- global monad structure
      --=======================================================

      -- preexistent objects 
      PureOb : 

        CatOb cat -> 
        ------------
        / Ob /

      -- preexistent morphisms 
      PureMor : 

        {a b : CatOb cat} ->
        a CatMor b -> 
        ---------------------------
        /(PureOb a) Mor (PureOb b)/

      -- preexistent equivalences 
      PureEqu : 

        {a b : CatOb cat} ->
        {f g : a CatMor b} ->
        f CatEqu g ->
        -----------------------------
        /(PureMor f) Equ (PureMor g)/

      -- restore preexistent identity morphisms 
      PureIdEqu : 

        (a : CatOb cat) ->
        -----------------------
        / PureMor (CatId a) Equ 
          IdMor (PureOb a) /

      -- restore preexistent multiplication of morphisms 
      _PureMulEqu_ : 

        {a b c : CatOb cat} ->
        (f : a CatMor b) -> 
        (g : b CatMor c) ->
        ------------------------------------
        / PureMor (f CatMul g) Equ 
          ((PureMor f) MulMor (PureMor g)) /

      --=======================================================
      -- terminal object structure
      --=======================================================

      -- terminal object
      TerminalOb : 

        ------
        / Ob /

      -- morphism to terminal object 
      TerminalMor : 

        (o : / Ob /) ->
        --------------------
        / o Mor TerminalOb /

      -- terminal morphism is natural 
      TerminalMorNatSquare : 

        {a b : / Ob /} ->
        (f : / a Mor b /) ->
        --------------------
        /(f MulMor TerminalMor b) Equ TerminalMor a /

      -- terminal morphism is unique 
      TerminalTriangleEqu : 

        ----------------------------
        / TerminalMor TerminalOb Equ 
          IdMor TerminalOb /

      --=======================================================
      -- binary product structure
      --=======================================================

      -- cartesian product of objects 
      _ProductOb_ : 

        (l r : / Ob {cat = cat}/) ->
        -----------------
        / Ob /

      -- cartesian product is functor 
      _ProductMor_ : 

        {l l' r r' : / Ob /} ->
        / l Mor l' / -> 
        / r Mor r' / ->
        ---------------------------------------
        /(l ProductOb r) Mor (l' ProductOb r')/

      -- left projection of product 
      _ProjectLeftMor_ : 

        (l r : / Ob /) ->
        ------------------------
        /(l ProductOb r) Mor l /

      -- right projection of product
      _ProjectRightMor_ : 

        (l r : / Ob /) ->
        ------------------------
        /(l ProductOb r) Mor r /

      -- diagonal morphism of product 
      DiagonalMor : 

        (o : / Ob /) ->
        ------------------------
        / o Mor (o ProductOb o)/

      -- left projection of product is natural 
      ProjectLeftMorNatSquare : 

        {l r l' r' : / Ob /} -> 
        (ml : / l Mor l' /) -> 
        (mr : / r Mor r' /) ->
        --------------------------
        /((ml ProductMor mr) MulMor (l' ProjectLeftMor r')) Equ 
          ((l ProjectLeftMor r) MulMor ml)/

      -- right projection of product is natural 
      ProjectRightMorNatSquare : 

        {l r l' r' : / Ob /} -> 
        (ml : / l Mor l' /) -> 
        (mr : / r Mor r' /) ->
        ---------------------------------------------------
        /((ml ProductMor mr) MulMor (l' ProjectRightMor r')) Equ 
          ((l ProjectRightMor r) MulMor mr)/

      -- diagonal of product is natural 
      DiagonalMorNatSquare : 

        {a b : / Ob /} ->
        (f : / a Mor b /) ->
        -----------------------------------------
        /(f MulMor (DiagonalMor b)) Equ 
          ((DiagonalMor a) MulMor (f ProductMor f))/

      -- cartesian product acts as congruence 
      ProductEqu : 

        {l l' r r' : / Ob /} ->
        {ml ml' : / l Mor l' /} -> 
        (mr mr' : / r Mor r' /) ->
        / ml Equ ml' / -> 
        / mr Equ mr' / ->
        ---------------------------------------------
        /(ml ProductMor mr) Equ (ml' ProductMor mr')/

      -- product is functorial on identities 
      _ProductIdEqu_ : 

        (l r : / Ob /) ->
        --------------------------------
        / (IdMor l ProductMor IdMor r) 
            Equ 
          IdMor (l ProductOb r) /

      -- product is functorial on composition 
      ProductMulEqu : 

        {la lb lc ra rb rc : / Ob /} ->
        (lf : / la Mor lb /) -> 
        (lg : / lb Mor lc /) -> 
        (rf : / ra Mor rb /) -> 
        (rg : / rb Mor rc /) ->
        --------------------------------------------------
        / ((lf MulMor lg) ProductMor (rf MulMor rg)) 
            Equ
          ((lf ProductMor rf) MulMor (lg ProductMor rg)) /

      -- 1st triangle of product adjunction 
      ProductTriangleEqu : 

        (l r : / Ob /) ->
        --------------------------------------------------------
        / (DiagonalMor (l ProductOb r)
            MulMor 
          ((l ProjectLeftMor r) ProductMor (l ProjectRightMor r))) 
              Equ 
          IdMor (l ProductOb r) /

      -- 2nd triangle of product adjunction 
      ProductTriangleLeftEqu : 

        (o : / Ob /) ->
        ---------------------------------------------
        / (DiagonalMor o MulMor (o ProjectLeftMor o)) 
            Equ 
          IdMor o /

      -- 2nd triangle of product adjunction OK
      ProductTriangleRightEqu : 

        (o : / Ob /) ->
        --------------------------------------------
        / (DiagonalMor o MulMor (o ProjectRightMor o)) 
            Equ 
          IdMor o /

      --=======================================================
      -- equalizer structure
      --=======================================================

      -- equalizer object 
      _EqualizerOb_ : 

        {a b : / Ob {cat = cat}/} ->
        (f g : / a Mor b /) ->
        ------------------
        / Ob /

      -- equalizer is functor 
      _EqualizerMor_ : 

        {a a' b b' : / Ob /} ->
        {f g : / a Mor b /} -> 
        {f' g' : / a' Mor b' /} ->
        {ma : / a Mor a' /} -> 
        {mb : / b Mor b' /} ->
        /(f MulMor mb) Equ (ma MulMor f')/ ->
        /(g MulMor mb) Equ (ma MulMor g')/ ->
        -------------------------------------------
        /(f EqualizerOb g) Mor (f' EqualizerOb g')/

      -- the unit of equalizer adjunction OK
      EqualizerUnitMor : 

        (a : / Ob /) ->
        --------------------------------------
        / a Mor (IdMor a EqualizerOb IdMor a)/

      -- the counit of equalizer adjunction, source 
      _EqualizerCounitSourceMor_ : 

        {a b : / Ob /} ->
        (f g : / a Mor b /) ->
        --------------------------
        /(f EqualizerOb g) Mor a /

      -- the counit of equalizer adjunction, target 
      _EqualizerCounitTargetMor_ : 

        {a b : / Ob /} ->
        (f g : / a Mor b /) ->
        --------------------------
        /(f EqualizerOb g) Mor b /

      -- com.square of equalizer count, left
      _EqualizerCounitLeftSquare_ : 

        {a b : / Ob /} ->
        (f g : / a Mor b /) ->
        ----------------------
        / (IdMor (f EqualizerOb g) MulMor (f EqualizerCounitTargetMor g))
            Equ 
          ((f EqualizerCounitSourceMor g) MulMor f)/

      -- com.square of equalizer count, right 
      _EqualizerCounitRightSquare_ : 

        {a b : / Ob /} ->
        (f g : / a Mor b /) ->
        ----------------------
        / (IdMor (f EqualizerOb g) MulMor (f EqualizerCounitTargetMor g))
            Equ 
          ((f EqualizerCounitSourceMor g) MulMor g)/

      -- equalizer unit morphism is natural 
      EqualizerUnitNatSquare : 

        {x y : / Ob /} ->
        (f : / x Mor y /) ->
        --------------------
        /(f MulMor EqualizerUnitMor y) 
            Equ 
          (EqualizerUnitMor x 
              MulMor 
            (((IdMorLeftNeutrEqu f) MulEqu InvEqu (IdMorRightNeutrEqu f)) 
                EqualizerMor 
             ((IdMorLeftNeutrEqu f) MulEqu InvEqu (IdMorRightNeutrEqu f))))/

      -- the counit of equalizer adjunction, source 
      _EqualizerCounitSourceNatSquare_ : 

        {a a' b b' : / Ob /} ->
        {f g : / a Mor b /} -> 
        {f' g' : / a' Mor b' /} ->
        {ma : / a Mor a' /} -> 
        {mb : / b Mor b' /} ->
        (ef : /(f MulMor mb) Equ (ma MulMor f')/) ->
        (eg : /(g MulMor mb) Equ (ma MulMor g')/) ->
        -------------------------------
        /((ef EqualizerMor eg) MulMor (f' EqualizerCounitSourceMor g')) 
            Equ 
          ((f EqualizerCounitSourceMor g) MulMor ma)/

      -- the counit of equalizer adjunction, target 
      _EqualizerCounitTargetNatSquare_ : 

        {a a' b b' : / Ob /} ->
        {f g : / a Mor b /} -> 
        {f' g' : / a' Mor b' /} ->
        {ma : / a Mor a' /} -> 
        {mb : / b Mor b' /} ->
        (ef : /(f MulMor mb) Equ (ma MulMor f')/) ->
        (eg : /(g MulMor mb) Equ (ma MulMor g')/) ->
        -------------------------------
        /((ef EqualizerMor eg) MulMor (f' EqualizerCounitTargetMor g')) 
            Equ 
          ((f EqualizerCounitTargetMor g) MulMor mb)/

      -- equalizer acts as congruence 
      _EqualizerEqu_ : 

        {a a' b b' : / Ob /} ->
        {f g : / a Mor b /} -> 
        {f' g' : / a' Mor b' /} ->
        {ma ma' : / a Mor a' /} -> 
        {mb mb' : / b Mor b' /} ->
        {ef : /(f MulMor mb) Equ (ma MulMor f')/} ->
        {ef' : /(f MulMor mb') Equ (ma' MulMor f')/} ->
        {eg : /(g MulMor mb) Equ (ma MulMor g')/} ->
        {eg' : /(g MulMor mb') Equ (ma' MulMor g')/} ->
        (ea : / ma Equ ma' /) -> 
        (eb : / mb Equ mb' /) -> 
        -------------------------------------------------
        /(ef EqualizerMor eg) Equ (ef' EqualizerMor eg')/

      -- equalizer is functorial on identities 
      _EqualizerIdEqu_ : 

        {a b : / Ob /} ->
        (f g : / a Mor b /) -> 
        --------------------------------------
        / (((IdMorRightNeutrEqu f) MulEqu InvEqu (IdMorLeftNeutrEqu f)) 
            EqualizerMor 
          ((IdMorRightNeutrEqu g) MulEqu InvEqu (IdMorLeftNeutrEqu g))) 
              Equ 
          IdMor (f EqualizerOb g) /

      -- equalizer is functorial on composition 
      EqualizerMulEqu : 

        {a a' a'' b b' b'' : / Ob /} ->
        {f g : / a Mor b /} -> 
        {f' g' : / a' Mor b' /} -> 
        {f'' g'' : / a'' Mor b'' /} ->
        {ma : / a Mor a' /} -> 
        {mb : / b Mor b' /} ->
        {ma' : / a' Mor a'' /} -> 
        {mb' : / b' Mor b'' /} ->
        (ef : /(f MulMor mb) Equ (ma MulMor f')/) ->
        (eg : /(g MulMor mb) Equ (ma MulMor g')/) ->
        (ef' : /(f' MulMor mb') Equ (ma' MulMor f'')/) ->
        (eg' : /(g' MulMor mb') Equ (ma' MulMor g'')/) ->
        ----------------------------------------------------
        / ((ef EqualizerMor eg) MulMor (ef' EqualizerMor eg'))
                    Equ
          ((MulMorAssocEqu 
              MulEqu 
            (ef MulMorEqu IdEqu mb') 
              MulEqu 
            InvEqu MulMorAssocEqu 
              MulEqu 
            (IdEqu ma MulMorEqu ef')
              MulEqu 
            MulMorAssocEqu)
                EqualizerMor 
            (MulMorAssocEqu
              MulEqu 
            (eg MulMorEqu IdEqu mb') 
              MulEqu 
            InvEqu MulMorAssocEqu 
              MulEqu 
            (IdEqu ma MulMorEqu eg')
              MulEqu 
            MulMorAssocEqu)) /

      -- equalizer, 1st triangle 
      EqualizerTriangle1Equ : 

        (x : / Ob /) ->
        --------------------------------------------------------------------
        / (EqualizerUnitMor x MulMor (IdMor x EqualizerCounitSourceMor IdMor x))
            Equ
          IdMor x /

      -- equalizer, 2nd triangle 
      EqualizerTriangle2Equ : 

        {a b : / Ob /} ->
        (f g : / a Mor b /) ->
        ----------------------------------
        / (EqualizerUnitMor (f EqualizerOb g) 
              MulMor 
          ((f EqualizerCounitLeftSquare g) EqualizerMor (f EqualizerCounitRightSquare g)))
            Equ
          IdMor (f EqualizerOb g) /


--=======================================================

--
-- pack it all into a CatRec
--
FreeFCCat : {level : Level} -> CatRec level -> CatRec level
FreeFCCat cat = record {
    cOb = Term (Ob {cat = cat});
    cMor = \a b -> Term (a Mor b);
    cEqu = \_ _ -> \f g -> Term (f Equ g);
    cId = IdMor;
    cMul = \_ _ _ -> _MulMor_
  }


