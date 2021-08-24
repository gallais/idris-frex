||| Constructing the frex of a monoid by a setoid
module Frexlet.Monoid.Frex.Construction

import Frex

import Frexlet.Monoid.Theory
import Frexlet.Monoid.Notation
import Frexlet.Monoid.Frex.Structure
import Frexlet.Monoid.Frex.Properties

import Notation.Multiplicative
import Notation.Action

import Data.List
import Data.List.Elem

import Data.Setoid.Pair
import Decidable.Equality

import Syntax.PreorderReasoning.Generic

%default total

public export
reifyElt : (a : Monoid) -> (s : Setoid) ->
           WithReified0 (U a) -> U s ->
           Term Signature (U a `Either` U s)
reifyElt a s Nothing  x = Done (Right x)
reifyElt a s (Just i) x =
  let %hint
      notation : Multiplicative1 (Term Signature (U a `Either` U s))
      notation = notationSyntax
  in Done (Left i) .*. Done (Right x)

-- Do we need something like this? A good quoting function would already
-- generate `call (MkOp Neutral) []` for neutral values wouldn't it?
public export
reflectElt :
  (a : Monoid) -> (s : Setoid) -> DecEq (U a) =>
  (U a `Either` U s) -> FrexCarrier a s
reflectElt a s (Right d) = a.dyn d
reflectElt a s (Left v) with (decEq v (a.sem Neutral))
  reflectElt a s (Left v) | Yes _ = a.sta Nothing
  reflectElt a s (Left v) | No _  = a.sta (Just v)

public export
normalFormElt : (a : Monoid) -> (s : Setoid) ->
  (i : WithReified0 (U a)) -> (x : U s) ->
  (FrexMonoid a s).rel
    ((FrexMonoid a s).Sem (reifyElt a s i x) (either (a.sta . Just) a.dyn))
    (ConsUlt i x $ Ultimate Nothing)
normalFormElt a s Nothing  x = (FrexMonoid a s).equivalence.reflexive ?
normalFormElt a s (Just y) x = (FrexMonoid a s).equivalence.reflexive ?

public export
reify : (a : Monoid) -> (s : Setoid) -> FrexCarrier a s ->
        Term Signature (U a `Either` U s)
reify a s (Ultimate Nothing)  = Call Unit []
reify a s (Ultimate (Just i)) = Done (Left i)
reify a s (ConsUlt  i x is) =
  let %hint
      notation : Multiplicative1 (Term Signature (U a `Either` U s))
      notation = notationSyntax
  in reifyElt a s i x .*. reify a s is

public export
normalForm : (a : Monoid) -> (s : Setoid) -> (is : FrexCarrier a s) ->
  (FrexMonoid a s).rel
    ((FrexMonoid a s).Sem (reify a s is) (either (a.sta . Just) a.dyn))
    is
normalForm a s (Ultimate Nothing)  = Ultimate $ a.equivalence.reflexive _
normalForm a s (Ultimate (Just i)) = Ultimate $ a.equivalence.reflexive _
normalForm a s (ConsUlt i x is) =
  let %hint
      notation : Multiplicative1 (Term Signature (U a `Either` U s))
      notation = notationSyntax
      %hint
      notation' : MAction1 (U a) (FrexCarrier a s)
      notation' = cast $ MonAction a s
      %hint
      notation'' : Multiplicative1 (U a)
      notation'' = a.Multiplicative1
      env : U a `Either` U s -> FrexCarrier a s
      env = either (a.sta . Just) a.dyn
  in CalcWith @{cast $ FrexMonoid a s} $
  |~ ((FrexMonoid a s).Sem (reifyElt a s i x) env)
     ++ ((FrexMonoid a s).Sem (reify a s is) env)
  <~ ConsUlt i x (Ultimate Nothing)
     ++ (FrexMonoid a s) .Sem (reify a s is) env
    ...( AppendHomomorphismProperty a s ? ? ? ?
           (normalFormElt a s i x)
           ((FrexMonoid a s).equivalence.reflexive ?)
       )
  <~ ConsUlt i x ((FrexMonoid a s) .Sem (reify a s is) env)
    ...( ConsUlt (a.equivalence.reflexive ?)
                 (s.equivalence.reflexive ?)
                 (multLftNeutrality a s Nothing (a.equivalence.reflexive ?) ?)
       )
  <~ ConsUlt i x is
    ...( ConsUlt (a.equivalence.reflexive ?)
                 (s.equivalence.reflexive ?)
                 (normalForm a s is)
       )

public export
staIsHomo : (a : Monoid) -> (s : Setoid) ->
            Homomorphism a.Algebra (FrexStructure a s) (a.sta . Just)
staIsHomo a s (MkOp Neutral) []    = Ultimate $ a.equivalence.reflexive ?
staIsHomo a s (MkOp Product) [i,j] = (FrexSetoid a s).equivalence.reflexive _

public export
staHomo : (a : Monoid) -> (s : Setoid) -> (a ~> FrexMonoid a s)
staHomo a s = MkSetoidHomomorphism
  { H = MkSetoidHomomorphism
    { H           = a.sta . Just
    , homomorphic = \i,j,prf => Ultimate prf
    }
  , preserves = staIsHomo a s
  }

public export
dynHomo : (a : Monoid) -> (s : Setoid) -> (s ~> FrexSetoid a s)
dynHomo a s = MkSetoidHomomorphism
  { H = a.dyn
  , homomorphic = \x,y,prf => (a.equivalence.reflexive _ , prf)
                              :: (FrexSetoid a s).equivalence.reflexive _
  }

public export
Extension : (a : Monoid) -> (s : Setoid) -> Extension a s
Extension a s = MkExtension
  { Model = FrexMonoid a s
  , Embed = staHomo a s
  , Var   = dynHomo a s
  }

public export
ExtenderPreservesProd :
  (a : Monoid) -> (s : Setoid) ->
  (other : Extension a s) ->
  (i, j : WithReified0 $ U a) ->
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
  in other.Model.rel
    (other.Embed.H.H $ unWithReified0 a (a.prod i j))
    (other.Embed.H.H (unWithReified0 a i)
     .*. other.Embed.H.H (unWithReified0 a j))
ExtenderPreservesProd a s other Nothing  j =
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
  in CalcWith @{cast other.Model} $
  |~ other.Embed.H.H (unWithReified0 a j)
  <~ other.Model.sem Neutral .*. other.Embed.H.H (unWithReified0 a j)
     ...( other.Model.equivalence.symmetric ? ?
            $ other.Model.validate LftNeutrality [_]
        )
  <~ other.Embed.H.H (a.sem Neutral) .*. other.Embed.H.H (unWithReified0 a j)
     ...( other.Model.equivalence.symmetric ? ?
           $ other.Model.cong 1 (Dyn 0 .*. Sta _) [_] [_]
             [other.Embed.preserves Unit []]
        )
ExtenderPreservesProd a s other (Just i) Nothing  =
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
  in CalcWith @{cast other.Model} $
  |~ other.Embed.H.H i
  <~ other.Embed.H.H i .*. other.Model.sem Neutral
     ...( other.Model.equivalence.symmetric ? ?
            $ other.Model.validate RgtNeutrality [_]
        )
  <~ other.Embed.H.H i .*. other.Embed.H.H (a.sem Neutral)
     ...( other.Model.equivalence.symmetric ? ?
           $ other.Model.cong 1 (Sta _ .*. Dyn 0) [_] [_]
             [other.Embed.preserves Unit []]
        )
ExtenderPreservesProd a s other (Just i) (Just j) =
  other.Embed.preserves Prod [i,j]

public export
ExtenderFunctionElt :
  (a : Monoid) -> (s : Setoid) ->
  (other : Extension a s) ->
  (i : WithReified0 $ U a) -> (x : U s) ->
  U other.Model
ExtenderFunctionElt a s other Nothing  x = other.Var.H x
ExtenderFunctionElt a s other (Just i) x =
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
  in other.Embed.H.H i .*. other.Var.H x

public export
ExtenderFunctionEltUnfold :
  (a : Monoid) -> (s : Setoid) ->
  (other : Extension a s) ->
  (i : WithReified0 $ U a) -> (x : U s) ->
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
  in other.Model.rel
    (ExtenderFunctionElt a s other i x)
    (other.Embed.H.H (unWithReified0 a i) .*. other.Var.H x)
ExtenderFunctionEltUnfold a s other Nothing  x =
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
  in CalcWith @{cast other.Model} $
  |~ other.Var.H x
  <~ other.Model.sem Neutral .*. other.Var.H x
     ...( other.Model.equivalence.symmetric ? ?
            $ other.Model.validate LftNeutrality [_]
        )
  <~ other.Embed.H.H (a.sem Neutral) .*. other.Var.H x
     ...( other.Model.equivalence.symmetric ? ?
           $ other.Model.cong 1 (Dyn 0 .*. Sta _) [_] [_]
             [other.Embed.preserves Unit []]
        )
ExtenderFunctionEltUnfold a s other (Just i) x =
  other.Model.equivalence.reflexive ?

public export
ExtenderFunction : (a : Monoid) -> (s : Setoid) ->
                   Frex.ExtenderFunction (Extension a s)
ExtenderFunction a s other (Ultimate i    ) =
  other.Embed.H.H (unWithReified0 a i)
ExtenderFunction a s other (ConsUlt i x is) =
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
  in ExtenderFunctionElt a s other i x
     .*. ExtenderFunction a s other is

public export
ExtenderEltPreservesMult :
  (a : Monoid) -> (s : Setoid) ->
  (other : Extension a s) ->
  (i, j : WithReified0 $ U a) -> (x : U s) ->
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
  in other.Model.rel
    (ExtenderFunctionElt a s other (a.prod i j) x)
    (other.Embed.H.H (unWithReified0 a i) .*. ExtenderFunctionElt a s other j x)
ExtenderEltPreservesMult a s other i j x =
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
  in CalcWith @{cast other.Model} $
  |~ ExtenderFunctionElt a s other (a.prod i j) x
  <~ other.Embed.H.H (unWithReified0 a (a.prod i j))
     .*. other.Var.H x
     ...( ExtenderFunctionEltUnfold a s other (a.prod i j) x )
  <~ other.Embed.H.H (unWithReified0 a i)
     .*. other.Embed.H.H (unWithReified0 a j)
     .*. other.Var.H x
     ...( other.Model.cong 1 (Dyn 0 .*. Sta _) [_] [_]
           [ExtenderPreservesProd a s other i j]
        )
  <~ other.Embed.H.H (unWithReified0 a i)
     .*. (other.Embed.H.H (unWithReified0 a j) .*. other.Var.H x)
     ...( other.Model.equivalence.symmetric ? ?
           $ other.Model.validate Associativity [_,_,_]
        )
  <~ other.Embed.H.H (unWithReified0 a i) .*. ExtenderFunctionElt a s other j x
     ...( other.Model.cong 1 (Sta _ .*. Dyn 0) [_] [_]
           [other.Model.equivalence.symmetric ? ?
             $ ExtenderFunctionEltUnfold a s other j x]
        )
public export
ExtenderPreservesMult : (a : Monoid) -> (s : Setoid) ->
  (other : Extension a s) ->
  (i : WithReified0 $ U a) -> (is : FrexCarrier a s) ->
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
  in other.Model.rel
    (ExtenderFunction a s other (a.mult i is))
    (other.Embed.H.H (unWithReified0 a i) .*. ExtenderFunction a s other is)
ExtenderPreservesMult a s other i (Ultimate j) =
  ExtenderPreservesProd a s other i j

ExtenderPreservesMult a s other i (ConsUlt j x js) =
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
  in CalcWith @{cast other.Model} $
  |~ ExtenderFunctionElt a s other (a.prod i j) x
     .*. ExtenderFunction a s other js
  <~ other.Embed.H.H (unWithReified0 a i) .*. ExtenderFunctionElt a s other j x
     .*. ExtenderFunction a s other js
     ...( other.Model.cong 1 (Dyn 0 .*. Sta _) [_] [_]
           [ExtenderEltPreservesMult a s other i j x]
        )
  <~ other.Embed.H.H (unWithReified0 a i)
     .*. (ExtenderFunctionElt a s other j x .*. ExtenderFunction a s other js)
     ...( other.Model.equivalence.symmetric ? ?
           $ other.Model.validate Associativity [_,_,_]
        )

-- Need to do this as a separate function so that the termination
-- checker can easily see the arguments decreasing.
public export
ExtenderPreservesProduct : (a : Monoid) -> (s : Setoid) ->
  (other : Extension a s) ->
  (is,js : FrexCarrier a s) ->
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
      %hint
      notation' : MAction1 (U a) (FrexCarrier a s)
      notation' = cast $ MonAction a s
      %hint
      notation'' : Multiplicative1 (U a)
      notation'' = a.Multiplicative1
      h : U (FrexMonoid a s) -> U other.Model
      h = ExtenderFunction a s other
  in other.Model.rel
    (h (is .*. js) )
    (h is .*. h js)
ExtenderPreservesProduct a s other (Ultimate i) js =
  ExtenderPreservesMult a s other i js
ExtenderPreservesProduct a s other (ConsUlt i x is) js =
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
      %hint
      notation' : MAction1 (U a) (FrexCarrier a s)
      notation' = cast $ MonAction a s
  in CalcWith @{cast other.Model} $
  |~ ExtenderFunctionElt a s other i x
     .*. ExtenderFunction a s other (is .*. js)
  <~ ExtenderFunctionElt a s other i x
     .*. (ExtenderFunction a s other is .*. ExtenderFunction a s other js)
     ...( other.Model.cong 1 (Sta _ .*. Dyn 0) [_] [_]
           [ExtenderPreservesProduct a s other is js]
        )
  <~ ExtenderFunctionElt a s other i x .*. ExtenderFunction a s other is
     .*. ExtenderFunction a s other js
     ...( other.Model.validate Associativity [_,_,_] )

public export
ExtenderIsHomomorphism : (a : Monoid) -> (s : Setoid) ->
  ExtenderIsHomomorphism (Extension a s) (ExtenderFunction a s)
ExtenderIsHomomorphism a s other (MkOp Neutral) []      =
  other.Embed.preserves Unit []
ExtenderIsHomomorphism a s other (MkOp Product) [is,js] =
  ExtenderPreservesProduct a s other is js

public export
ExtenderIsSetoidHomomorphism : (a : Monoid) -> (s : Setoid) -> (other : Extension a s) ->
  (is,js : FrexCarrier a s) ->
  (prf : (FrexMonoid a s).rel is js) ->
  other.Model.rel
    (ExtenderFunction a s other is)
    (ExtenderFunction a s other js)
ExtenderIsSetoidHomomorphism a s other (Ultimate i) (Ultimate j)
  (Ultimate i_eq_j) = other.Embed.H.homomorphic ? ? i_eq_j
ExtenderIsSetoidHomomorphism a s other (ConsUlt i x is) (ConsUlt j y js)
  (ConsUlt i_eq_j x_eq_y is_eq_js) =
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
  in CalcWith @{cast other.Model} $
  |~ ExtenderFunctionElt a s other i x .*. ExtenderFunction a s other is
  <~ other.Embed.H.H (unWithReified0 a i) .*. other.Var.H x
     .*. ExtenderFunction a s other is
     ...( other.Model.cong 1 (Dyn 0 .*. Sta _) [_] [_]
           [ExtenderFunctionEltUnfold a s other i x]
        )
  <~ other.Embed.H.H (unWithReified0 a j) .*. other.Var.H y
     .*. ExtenderFunction a s other js
     ...( other.Model.cong 3 (Dyn 0 .*. Dyn 1 .*. Dyn 2) [_,_,_] [_,_,_]
          [ other.Embed.H.homomorphic              ?  ?  i_eq_j
          , other.Var.homomorphic                  x  y  x_eq_y
          , ExtenderIsSetoidHomomorphism a s other is js is_eq_js ]
        )
  <~ ExtenderFunctionElt a s other j y .*. ExtenderFunction a s other js
     ...( other.Model.cong 1 (Dyn 0 .*. Sta _) [_] [_]
           [other.Model.equivalence.symmetric ? ?
             $ ExtenderFunctionEltUnfold a s other j y]
        )

public export
ExtenderHomomorphism : (a : Monoid) -> (s : Setoid) -> Frex.Frex.ExtenderHomomorphism (Extension a s)
ExtenderHomomorphism a s other = MkSetoidHomomorphism
  { H = MkSetoidHomomorphism
      { H = ExtenderFunction a s other
      , homomorphic = ExtenderIsSetoidHomomorphism a s other
      }
  , preserves = ExtenderIsHomomorphism a s other
  }

public export
ExtenderPreservesEmbedding : (a : Monoid) -> (s : Setoid) ->
  ExtenderPreservesEmbedding (Extension a s) (ExtenderHomomorphism a s)
ExtenderPreservesEmbedding a s other i = other.Model.equivalence.reflexive _

public export
ExtenderPreservesVars : (a : Monoid) -> (s : Setoid) ->
  ExtenderPreservesVars (Extension a s) (ExtenderHomomorphism a s)
ExtenderPreservesVars a s other x =
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
  in CalcWith @{cast other.Model} $
  |~ other.Var.H x .*. other.Embed.H.H (a.sem Neutral)
  <~ other.Var.H x .*. other.Model.sem Neutral
     ...( other.Model.cong 1 (Sta _ .*. Dyn 0) [_] [_]
            [other.Embed.preserves Unit []]
        )
  <~ other.Var.H x
     ...( other.Model.validate RgtNeutrality [_] )

public export
Extender : (a : Monoid) -> (s : Setoid) -> Extender (Extension a s)
Extender a s other = MkExtensionMorphism
  { H             = ExtenderHomomorphism       a s other
  , PreserveEmbed = ExtenderPreservesEmbedding a s other
  , PreserveVar   = ExtenderPreservesVars      a s other
  }

public export
Uniqueness : (a : Monoid) -> (s : Setoid) -> Uniqueness (Extension a s)
Uniqueness a s other extend1 extend2 is =
  ?goal

{-
  let frex : Extension a s
      frex = Extension a s
      lemma1 : (extend : frex ~> other) -> (is : U frex.Model) ->
        other.Model.rel
          (extend.H.H.H is)
          (other.Model.Sem (reify a s is) (extend.H.H.H . (either a.sta a.dyn)))
      lemma1 extend is = CalcWith @{cast other.Model} $
        |~ extend.H.H.H is
        <~ extend.H.H.H (frex.Sem (reify a s is) (either a.sta a.dyn))
             ...( other.Model.equivalence.symmetric _ _
                $ extend.H.H.homomorphic _ _
                $ normalForm a s is)
        <~ other.Model.Sem (reify a s is) (extend.H.H.H . (either a.sta a.dyn))
             ...(homoPreservesSem extend.H _ _)
      lemma2 : ((cast a `Either` s) ~~> cast other.Model).equivalence.relation
                  (extend1.H.H . (either frex.Embed.H frex.Var))
                  (extend2.H.H . (either frex.Embed.H frex.Var))
      lemma2 (Left  i) = CalcWith @{cast other.Model} $
        |~ extend1.H.H.H (either frex.Embed.H.H frex.Var.H (Left i))
        ~~ extend1.H.H.H (frex.Embed.H.H i)  ...(Refl)
        <~ other.Embed.H.H i                 ...(extend1.PreserveEmbed i)
        <~ extend2.H.H.H (frex.Embed.H.H i)  ...(other.Model.equivalence.symmetric _ _ $
                                                 extend2.PreserveEmbed i)
        ~~ extend2.H.H.H (either frex.Embed.H.H frex.Var.H (Left i))
                                             ...(Refl)
      lemma2 (Right x) = CalcWith @{cast other.Model} $
        |~ extend1.H.H.H (either frex.Embed.H.H frex.Var.H (Right x))
        ~~ extend1.H.H.H (frex.Var.H x) ...(Refl)
        <~ other.Var.H x                ...(extend1.PreserveVar x)
        <~ extend2.H.H.H (frex.Var.H x) ...(other.Model.equivalence.symmetric _ _ $
                                            extend2.PreserveVar x)
        ~~ extend2.H.H.H (either frex.Embed.H.H frex.Var.H (Right x))
                                        ...(Refl)
  in CalcWith @{cast other.Model} $
  |~ extend1.H.H.H is
  <~ other.Model.Sem (reify a s is) (extend1.H.H.H . (either a.sta a.dyn))
       ...(lemma1 extend1 is)
  <~ other.Model.Sem (reify a s is) (extend2.H.H.H . (either a.sta a.dyn))
       ...((eval (reify a s is)).homomorphic
             (extend1.H.H . (either frex.Embed.H frex.Var))
             (extend2.H.H . (either frex.Embed.H frex.Var))
             $ lemma2)
  <~ extend2.H.H.H is ...(other.Model.equivalence.symmetric _ _ $ lemma1 extend2 is)
-}

public export
MonoidFrex : (a : Monoid) -> (s : Setoid) -> Frex a s
MonoidFrex a s = MkFrex
  { Data = Extension a s
  , UP   = IsUniversal
     { Exists = Extender a s
     , Unique = Uniqueness a s
     }
  }
