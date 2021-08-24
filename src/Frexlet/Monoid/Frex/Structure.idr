||| The structure of the frex for (mere) monoids
||| Its elements are given by a 'polynomial' of the form:
|||
||| an * xn * ... a1 * x1 * a0
|||
||| Its unit is 1, and multiplication is given by:
|||
||| (an * xn * ... a1 * x1 * a0) *(bm * ym * ... b1 * y1 * b0)
||| := an * xn * ... a1 * x1 * (a0*bm) * ym ... * y1 * b0
|||
||| and some care is required for the edge cases.
module Frexlet.Monoid.Frex.Structure


import Frex

import Frexlet.Monoid.Theory
import Frexlet.Monoid.Notation

import Notation.Multiplicative
import Notation.Action

import Data.List
import Data.List.Elem

import Data.Setoid.Pair

%default total

public export
||| A monoid enriched with a reified version of its neutral element
WithReified0 : Type -> Type
WithReified0 = Maybe

public export
unWithReified0 : (a : Monoid) -> WithReified0 (U a) -> U a
unWithReified0 a = fromMaybe (a.sem Neutral)

public export
0 WithReified0Equivalence : (a : Monoid) -> Rel (WithReified0 $ U a)
WithReified0Equivalence a
  = a.rel `on` unWithReified0 a

public export
WithReified0Setoid : Monoid -> Setoid
WithReified0Setoid a = MkSetoid (WithReified0 $ U a) $ MkEquivalence
  { relation   = WithReified0Equivalence a
  , reflexive  = \ x => a.equivalence.reflexive ?
  , symmetric  = \ x, y => a.equivalence.symmetric ? ?
  , transitive = \ x, y, z => a.equivalence.transitive ? ? ?
  }

||| A list of elements alternating between two types starting and
||| ending with an `ult`imate.
public export
data UltList : (pen, ult : Type) -> Type where
  Ultimate : (i : ult) -> UltList pen ult
  ConsUlt : (i : ult) -> (x : pen) -> UltList pen ult -> UltList pen ult
-- Smart constructors so we can get a list notation, and we don't have
-- to think too much about the parity of the list
namespace Hack
  public export
  Nil : Unit
  Nil = ()

  public export
  (::) : ult -> Unit -> UltList pen ult
  (::) x _ = Ultimate x

namespace Ult
  public export
  (::) : (ult , pen) -> UltList pen ult -> UltList pen ult
  (::) = Prelude.uncurry ConsUlt

%name UltList is,js,ks,ells

public export
mergeWith : (a -> a -> a) -> (l, r : Maybe a) -> Maybe a
mergeWith f (Just l) (Just r) = Just (f l r)
mergeWith f l r  = l <|> r

public export
(.prod) : (a : Monoid) -> (x, y : WithReified0 (U a)) -> WithReified0 (U a)
a.prod = mergeWith (a.sem Product)

public export
prodUnfold : (a : Monoid) -> (x, y : WithReified0 (U a)) ->
  WithReified0Equivalence a
    (a.prod x y)
    (Just $ a.sem Product (unWithReified0 a x) (unWithReified0 a y))
prodUnfold a Nothing  y
  = a.equivalence.symmetric ? ?
  $ a.validate LftNeutrality [?]
prodUnfold a (Just x) Nothing
  = a.equivalence.symmetric ? ?
  $ a.validate RgtNeutrality [?]
prodUnfold a (Just x) (Just y)
  = a.equivalence.reflexive ?

public export
prodCong : (a : Monoid) -> (x, y, s, t : WithReified0 (U a)) ->
  WithReified0Equivalence a x s ->
  WithReified0Equivalence a y t ->
  WithReified0Equivalence a
    (a.prod x y)
    (a.prod s t)
prodCong a x y s t xeqs yeqt
  = a.equivalence.transitive ? ? ?
      (prodUnfold a x y)
  $ a.equivalence.transitive ? ? ?
      (a.cong 2 (Dyn 0 .*. Dyn 1) [_,_] [_,_] [xeqs, yeqt])
  $ a.equivalence.symmetric ? ?
  $ prodUnfold a s t

public export
(.mult) : (a : Monoid) -> Maybe (U a) -> UltList pen (WithReified0 $ U a) ->
          UltList pen (WithReified0 $ U a)
a.mult mi (Ultimate mj) = Ultimate (a.prod mi mj)
a.mult mi (ConsUlt mj x is) = (a.prod mi mj, x) :: is

public export
(++)  : {a : Monoid} -> (is, js : UltList pen (WithReified0 $ U a)) ->
        UltList pen (WithReified0 $ U a)
(++) (Ultimate mi) js = a.mult mi js
(++) (ConsUlt mi x is) js = (mi , x) :: is ++ js

namespace Equality
  ||| Equality for UltList pen ult
  public export
  data UltListEquality :
         {pen,ult : Type} -> (penRel : pen -> pen -> Type)
      -> (ultRel : ult -> ult -> Type) -> (is, js : UltList pen ult) -> Type where
    [search penRel ultRel]
    Ultimate : forall penRel, ultRel.
      ultRel i j -> UltListEquality penRel ultRel (Ultimate i) (Ultimate j)
    ConsUlt  : forall penRel, ultRel. ultRel i j ->
               penRel x y ->
               UltListEquality penRel ultRel is js ->
               UltListEquality penRel ultRel ((i,x) :: is) ((j,y) :: js)

  -- Again, smart constructors so that we can avoid thinking about parity sometimes
  namespace Hack
    public export
    (::) : forall penRel, ultRel.
           ultRel i j -> Unit -> UltListEquality penRel ultRel (Ultimate i) (Ultimate j)
    (::) prf _ = Ultimate prf

  namespace Ult
    public export
    (::) : forall penRel, ultRel.
           ( ultRel i j
           , penRel x y
           ) -> UltListEquality penRel ultRel is js ->
      UltListEquality penRel ultRel ((i,x) :: is) ((j,y) :: js)
    (::) = Prelude.uncurry ConsUlt

---------------------- Equality on alternating is an equivalence
  ----------------- Reflexivity --------------------------
  public export
  UltListReflexive : (pen, ult : Setoid) -> (is : UltList (U pen) (U ult))
    -> UltListEquality pen.equivalence.relation ult.equivalence.relation is is

  UltListReflexive pen ult (Ultimate i) = Ultimate (ult.equivalence.reflexive i)
  UltListReflexive pen ult (ConsUlt i x is) =
    ( ult.equivalence.reflexive i
    , pen.equivalence.reflexive x
    ) :: UltListReflexive pen ult is

  ----------------- Symmetry --------------------------
  public export
  UltListSymmetric : (pen, ult : Setoid) -> (is,js : UltList (U pen) (U ult)) ->
    (prf : UltListEquality pen.equivalence.relation ult.equivalence.relation is js) ->
    UltListEquality pen.equivalence.relation ult.equivalence.relation js is

  UltListSymmetric pen ult (Ultimate i) (Ultimate j) (Ultimate prf) =
    Ultimate $ ult.equivalence.symmetric i j prf
  UltListSymmetric pen ult (ConsUlt i x is) (ConsUlt j y js)
    (ConsUlt prf1 prf2 prf3) =
    ( ult.equivalence.symmetric i j prf1
    , pen.equivalence.symmetric x y prf2
    ) :: UltListSymmetric pen ult is js prf3

  ---------------- Transitivity ------------------------
  public export
  UltListTransitive : (pen, ult : Setoid) -> (is,js,ks : UltList (U pen) (U ult)) ->
    (prf1 : UltListEquality pen.equivalence.relation ult.equivalence.relation is js) ->
    (prf2 : UltListEquality pen.equivalence.relation ult.equivalence.relation js ks) ->
    UltListEquality
      pen.equivalence.relation
      ult.equivalence.relation
      is ks

  UltListTransitive pen ult (Ultimate i) (Ultimate j) (Ultimate k) (Ultimate prf1) (Ultimate prf2)
    = Ultimate $ ult.equivalence.transitive i j k prf1 prf2
  UltListTransitive pen ult (ConsUlt i x is) (ConsUlt j y js) (ConsUlt k z ks)
    (ConsUlt prf11 prf12 prf13) (ConsUlt prf21 prf22 prf23) =
    ( ult.equivalence.transitive i j k prf11 prf21
    , pen.equivalence.transitive x y z prf12 prf22
    ) :: UltListTransitive pen ult is js ks prf13 prf23

public export
UltListSetoid : (pen, ult : Setoid) -> Setoid
UltListSetoid pen ult = MkSetoid (UltList (U pen) (U ult)) $ MkEquivalence
  { relation   = UltListEquality   pen.equivalence.relation
                                   ult.equivalence.relation
  , reflexive  = UltListReflexive  pen ult
  , symmetric  = UltListSymmetric  pen ult
  , transitive = UltListTransitive pen ult
  }

public export
MultHomomorphism : (a : Monoid) -> (s : Setoid) ->
  SetoidHomomorphism
    (cast (WithReified0Setoid a) `Pair` UltListSetoid s (cast $ WithReified0Setoid a))
    (UltListSetoid s (cast (WithReified0Setoid a)))
    (Prelude.uncurry a.mult)
MultHomomorphism a s (i, Ultimate i1) (j, Ultimate j1)
  (MkAnd i_eq_j $ Ultimate i1_eq_i2)
  = Ultimate $ prodCong a ? ? ? ? i_eq_j i1_eq_i2
MultHomomorphism a s (i, ConsUlt i1 x is) (j,ConsUlt j1 y js)
  (MkAnd i_eq_j $ ConsUlt i1_eq_i2 x_eq_y is_eq_js)
  = ( prodCong a ? ? ? ? i_eq_j i1_eq_i2
    , x_eq_y
    ) :: is_eq_js
MultHomomorphism _ _ (_, Ultimate _) (_, ConsUlt _ _ _) (MkAnd _ _) impossible
MultHomomorphism _ _ (_, ConsUlt _ _ _) (_, Ultimate _) (MkAnd _ _) impossible

public export
AppendHomomorphismProperty : (a : Monoid) -> (x : Setoid) ->
  (is1, is2, js1, js2 : UltList (U x) (WithReified0 $ U a)) ->
  (UltListSetoid x (cast $ WithReified0Setoid a)).equivalence.relation
    is1
    is2 ->
  (UltListSetoid x (cast $ WithReified0Setoid a)).equivalence.relation
    js1
    js2 ->
  (UltListSetoid x (cast $ WithReified0Setoid a)).equivalence.relation
    ((++) {a} is1 js1)
    ((++) {a} is2 js2)

AppendHomomorphismProperty a s (Ultimate i0     ) (Ultimate j0     ) is  js
  (Ultimate i0_eq_j0) is_eq_js
  =  MultHomomorphism a s (i0, is) (j0, js) (MkAnd i0_eq_j0 is_eq_js)
AppendHomomorphismProperty a s (ConsUlt i0 x is0) (ConsUlt j0 y js0) is1 js1
  (ConsUlt i0_eq_j0 x_eq_y is0_eq_js0) is1_eq_js1 =
  ( i0_eq_j0
  , x_eq_y
  ) :: AppendHomomorphismProperty a s is0 js0 is1 js1 is0_eq_js0 is1_eq_js1

public export
AppendHomomorphism : (a : Monoid) -> (x : Setoid) ->
  SetoidHomomorphism
    (UltListSetoid x (cast $ WithReified0Setoid a) `Pair`
     UltListSetoid x (cast $ WithReified0Setoid a))
    (UltListSetoid x (cast $ WithReified0Setoid a))
    (Prelude.uncurry ((++) {a}))
AppendHomomorphism a x (is1,js1) (is2,js2) (MkAnd is1_eq_is2 js1_eq_js2)
  = AppendHomomorphismProperty a x is1 is2 js1 js2 is1_eq_is2 js1_eq_js2

public export 0
FrexCarrier : (a : Monoid) -> (x : Setoid) -> Type
FrexCarrier a x = UltList (U x) (WithReified0 $ U a)

||| Embedding of concrete elements in the frex by identifying
||| i with the singleton i
public export
(.sta) : (a : Monoid) -> Maybe (U a) -> UltList x (WithReified0 $ U a)
(.sta) a = Ultimate

||| Embedding variables in the frex by identifying
||| x with 1 * x * 1
public export
(.dyn) : (a : Monoid) -> x -> UltList x (WithReified0 $ U a)
(.dyn) a v = (Nothing , v) :: a.sta Nothing

public export
FrexAlgebraStructure : (a : Monoid) -> (x : Setoid) ->
                       Signature `algebraOver'` (FrexCarrier a x)
FrexAlgebraStructure a x Neutral = a.sta Nothing
FrexAlgebraStructure a x Product = (++) {a}

public export
FrexStructure : (a : Monoid) -> (x : Setoid) -> MonoidStructure
FrexStructure a x = MkSetoidAlgebra
    { algebra = MkAlgebra (FrexCarrier a x) (FrexAlgebraStructure a x)
    , equivalence = (UltListSetoid x (cast $ WithReified0Setoid a)).equivalence
    , congruence = \case
        MkOp Neutral => \_,_,_ => (UltListSetoid x (cast  $ WithReified0Setoid a)).equivalence.reflexive _
        MkOp Product => \ [is1,js1],[is2,js2],prf =>
          AppendHomomorphism a x (is1,js1) (is2,js2) (MkAnd (prf 0) (prf 1))
    }

public export
FrexSetoid : (a : Monoid) -> (x : Setoid) -> Setoid
FrexSetoid a x = cast $ FrexStructure a x

public export
MonAction : (a : Monoid) -> (s : Setoid) -> ActionData (U a) (FrexCarrier a s)
MonAction a s =
  [ a.mult . Just
  , (FrexStructure a s).sem Neutral
  , (FrexStructure a s).sem Product
  ]
