||| Properties of the monoid frexlet and its operations
module Frexlet.Monoid.Frex.Properties

import Frex

import Frexlet.Monoid.Theory
import Frexlet.Monoid.Notation
import Frexlet.Monoid.Frex.Structure

import Notation.Multiplicative
import Notation.Action

import Data.List
import Data.List.Elem

import Data.Setoid.Pair

%default total

----------------------------- .mult properties
-- Neutral has two representations:
-- 1. Nothing
-- 2. Just (a.sem Neutral)
-- So we state a lemma generic in the notion of neutral being used

public export
prodLftNeutrality : (a : Monoid) ->
  (neutral, i : WithReified0 $ U a) ->
  WithReified0Equivalence a neutral Nothing ->
  WithReified0Equivalence a
    (a.prod neutral i)
    i
prodLftNeutrality a neutral i eq
  = a.equivalence.transitive ? ? ?
     (prodUnfold a ? ?)
  $ a.equivalence.transitive ? ? ?
     (a.cong 1 (Dyn 0 .*. Sta _) [_] [_] [eq])
  $ a.validate LftNeutrality [_]

public export
prodRgtNeutrality : (a : Monoid) ->
  (neutral, i : WithReified0 $ U a) ->
  WithReified0Equivalence a neutral Nothing ->
  WithReified0Equivalence a
    (a.prod i neutral)
    i
prodRgtNeutrality a neutral i eq
  = a.equivalence.transitive ? ? ?
     (prodUnfold a ? ?)
  $ a.equivalence.transitive ? ? ?
     (a.cong 1 (Sta _ .*. Dyn 0) [_] [_] [eq])
  $ a.validate RgtNeutrality [_]

public export
multLftNeutrality : (a : Monoid) -> (s : Setoid) ->
  (neutral : WithReified0 $ U a) ->
  WithReified0Equivalence a neutral Nothing ->
  (is : FrexCarrier a s) ->
  let %hint
      notation : MAction1 (U a) (FrexCarrier a s)
      notation = cast $ MonAction a s
      %hint
      notation' : Multiplicative1 (U a)
      notation' = a.Multiplicative1
  in (FrexSetoid a s).equivalence.relation
       (a.mult neutral is)
       is
multLftNeutrality a s neutral eq (Ultimate i)
  = Ultimate $ prodLftNeutrality a neutral i eq
multLftNeutrality a s neutral eq (ConsUlt i x is) =
  ( prodLftNeutrality a neutral i eq
  , s.equivalence.reflexive _
  ) :: (FrexSetoid a s).equivalence.reflexive _

public export
prodAssociative : (a : Monoid) ->
  (i0, i1, i : WithReified0 $ U a) ->
  WithReified0Equivalence a
    (a.prod i0 $ a.prod i1 i)
    (a.prod (a.prod i0 i1) i)
prodAssociative a i0 i1 i
  = a.equivalence.transitive ? ? ?
     (a.equivalence.transitive ? ? ?
       (prodUnfold a ? ?)
       (a.cong 1 (Sta _ .*. Dyn 0) [_] [_] [prodUnfold a ? ?]))
  $ a.equivalence.transitive ? ? ?
    (a.validate Associativity [_,_,_])
  $ a.equivalence.symmetric ? ?
  $ a.equivalence.transitive ? ? ?
    (prodUnfold a ? ?)
    (a.cong 1 (Dyn 0 .*. Sta _) [_] [_] [prodUnfold a ? ?])

public export
multAssociative : (a : Monoid) -> (s : Setoid) ->
  (i0, i1 : WithReified0 $ U a) -> (is : FrexCarrier a s) ->
  (FrexSetoid a s).equivalence.relation
    (a.mult i0 $ a.mult i1 is)
    (a.mult (a.prod i0 i1) is)
multAssociative a s i0 i1 (Ultimate i)
  = Ultimate $ prodAssociative a i0 i1 i
multAssociative a s i0 i1 (ConsUlt i x is) =
  ( prodAssociative a i0 i1 i
  , s.equivalence.reflexive _
  ) :: (FrexSetoid a s).equivalence.reflexive _

public export
multMultAssociative : (a : Monoid) -> (s : Setoid) ->
  (i0 : WithReified0 $ U a) -> (is,js : FrexCarrier a s) ->
  let %hint
      notation : MAction1 (U a) (FrexCarrier a s)
      notation = cast $ MonAction a s
  in (FrexSetoid a s).equivalence.relation
       (a.mult i0 (is .*. js))
       ((a.mult i0 is) .*. js)
multMultAssociative a s i0 (Ultimate i1    ) js
  = multAssociative a s i0 i1 js
multMultAssociative a s i0 (ConsUlt i1 x is) js
  = (FrexSetoid a s).equivalence.reflexive _

----------------------------- append properties
public export
appendUnitLftNeutral : (a : Monoid) -> (s : Setoid) -> (is : FrexCarrier a s) ->
  let %hint
      notation : MAction1 (U a) (FrexCarrier a s)
      notation = cast $ MonAction a s
  in (FrexSetoid a s).equivalence.relation
    (I1 .*. is)
    is
appendUnitLftNeutral a s is
  = multLftNeutrality a s Nothing (a.equivalence.reflexive ?) is

public export
appendUnitRgtNeutral : (a : Monoid) -> (s : Setoid) -> (is : FrexCarrier a s) ->
  let %hint
      notation : MAction1 (U a) (FrexCarrier a s)
      notation = cast $ MonAction a s
  in (FrexSetoid a s).equivalence.relation
    (is .*. I1)
    is
appendUnitRgtNeutral a s (Ultimate i)
  = Ultimate $ prodRgtNeutrality a Nothing i (a.equivalence.reflexive ?)
appendUnitRgtNeutral a s (ConsUlt i x is) =
  ( a.equivalence.reflexive ?
  , s.equivalence.reflexive x
  ) :: appendUnitRgtNeutral a s is

public export
appendAssociative : (a : Monoid) -> (s : Setoid) -> (is,js,ks : FrexCarrier a s) ->
  let %hint
      notation : MAction1 (U a) (FrexCarrier a s)
      notation = cast $ MonAction a s
  in (FrexSetoid a s).equivalence.relation
    (is .*. (js .*. ks))
    ((is .*. js) .*. ks)
appendAssociative a s (Ultimate i) js ks = multMultAssociative a s i js ks
appendAssociative a s (ConsUlt i x is) js ks =
  ( a.equivalence.reflexive _
  , s.equivalence.reflexive _
  ) :: appendAssociative a s is js ks

-----------------------------------------------------------------

public export
FrexValidatesAxioms : (a : Monoid) -> (s : Setoid) -> Validates MonoidTheory (FrexStructure a s)
FrexValidatesAxioms a s LftNeutrality env = appendUnitLftNeutral a s (env 0)
FrexValidatesAxioms a s RgtNeutrality env = appendUnitRgtNeutral a s (env 0)
FrexValidatesAxioms a s Associativity env = appendAssociative    a s (env 0) (env 1) (env 2)

public export
FrexMonoid : (a : Monoid) -> (s : Setoid) -> Monoid
FrexMonoid a s = MkModel
  { Algebra = FrexStructure a s
  , Validate = FrexValidatesAxioms a s
  }
