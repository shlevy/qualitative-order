module QualitativeOrder.Examples

import QualitativeOrder.Core

%default total
%access public export

namespace nat_order
  ||| Relate two nats to a third nat as their difference
  data Sub : (subtrahend : Nat) -> (minuend : Nat) -> (difference : Nat) -> Type where
    ||| Anything minus 0 is the thing itself
    SubZero : Sub Z right right
    ||| If x - y = z, (S x) - (S y) = Z
    SubSucc : Sub left right res -> Sub (S left) (S right) res

  ||| `Sub` is a QualitativeOrder for nats
  NatOrder : QualitativeOrder Nat Sub
  NatOrder = MkQualitativeOrder reflexive antisymmetric transitive NatOrder
    where
      reflexive' : (x : Nat) -> Sub x x Z
      reflexive' Z = SubZero
      reflexive' (S n) = SubSucc (reflexive' n)

      reflexive : (y : Nat ** ((x : Nat) -> Sub x x y))
      reflexive = (Z ** reflexive')

      antisymmetric : (x : Nat) -> (y : Nat) -> (n : Nat) -> (m : Nat) -> Sub x y n -> Sub y x m -> x = y
      antisymmetric _ _ _ _ SubZero SubZero = Refl
      antisymmetric _ _ _ _ (SubSucc x) (SubSucc y) = cong (antisymmetric _ _ _ _ x y)

      transitive : (x : Nat) -> (y : Nat) -> (z : Nat) -> (n : Nat) -> (m : Nat) -> Sub x y n -> Sub y z m -> (w : Nat ** Sub x z w)
      transitive _ _ z _ _ SubZero _ = (z ** SubZero)
      transitive _ _ _ _ _ (SubSucc x) (SubSucc y) with (transitive _ _ _ _ _ x y)
        | (w ** s) = (w ** SubSucc s)
