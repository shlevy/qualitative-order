||| Examples of qualitative orders
module QualitativeOrder.Examples

import QualitativeOrder.Core

%default total
%access public export

namespace nat_order
  ||| Relate two nats to a third nat as their difference
  data Sub : (subtrahend : Nat) ->
             (minuend : Nat) ->
             (difference : Nat) ->
             Type where
    ||| Anything minus 0 is the thing itself
    SubZero : Sub Z right right
    ||| If x - y = z, (S x) - (S y) = Z
    SubSucc : Sub left right res -> Sub (S left) (S right) res

  ||| Stream of the sub order
  SubStream : OrderStream Nat
  SubStream = Sub :: SubStream

  ||| The sub stream is qualitative
  SubStreamQualitative : Qualitative SubStream
  SubStreamQualitative =
      MkQualitative reflexive antisymmetric transitive SubStreamQualitative
    where
      reflexive' : (x : Nat) -> Sub x x Z
      reflexive' Z = SubZero
      reflexive' (S n) = SubSucc (reflexive' n)

      reflexive : Reflexive Sub
      reflexive = (Z ** reflexive')

      antisymmetric : Antisymmetric Sub
      antisymmetric _ _ _ _ SubZero SubZero = Refl
      antisymmetric _ _ _ _ (SubSucc x) (SubSucc y) =
        cong (antisymmetric _ _ _ _ x y)

      transitive : Transitive Sub
      transitive _ _ z _ _ SubZero _ = (z ** SubZero)
      transitive _ _ _ _ _ (SubSucc x) (SubSucc y)
        with (transitive _ _ _ _ _ x y)
          | (w ** s) = (w ** SubSucc s)
