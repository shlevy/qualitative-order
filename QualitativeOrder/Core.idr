||| Core definitions for working with qualitative orders
module QualitativeOrder.Core

%default total
%access public export

||| A (partial) ordering of a type with infinitely deep higher order ordering
|||
||| Called a qualitative order because it's intended to model differences along a single dimension where quantitative relationships are unavailable but we still have qualitative differences of degree.
||| @ type The type being ordered
record QualitativeOrder (type : Type) where
  ||| Make a qualitative order
  constructor MkQualitativeOrder

  ||| Some type that relates two elements of the ordered type to one of its order type
  ||| @ lesser The smaller element
  ||| @ greater The greater element
  ||| @ order_class The class of the relationship between `lesser` and `greater`
  relation : (lesser : type) -> (greater : type) -> (order_class : order_classes) -> Type

  ||| `relation` is reflexive
  |||
  ||| There is some order class `y` such that `relation x x y` holds for all `x` in `type`
  reflexive : (y : order_classes ** ((x : type) -> (relation x x y)))

  ||| `relation` is antisymmetric
  |||
  ||| If `x` is less than `y` (in any class) and `y` is less than `x` (in any class) then `x` = `y`
  |||
  ||| I want `x`, `y`, `n`, and `m` to be implicit here, but Idris doesn't like it
  antisymmetric : ((x : type) -> (y : type) -> (n : order_classes) -> (m : order_classes) -> (relation x y n) -> (relation y x m) -> x = y)

  ||| `relation` is transitive
  |||
  ||| If `x` is less than `y` (in any class) and `y` is less than `z` (in any class), then `x` is less than `z` in some class `w`
  |||
  ||| I want `x`, `y`, `z`, `n`, and `m` to be implicit here, but Idris doesn't like it
  transitive : ((x : type) -> (y : type) -> (z : type) -> (n : order_classes) -> (m : order_classes) -> (relation x y n) -> (relation y z m) -> (w : order_classes ** relation x z w))

  ||| The type of order classes is itself qualitatively ordered (and so on ad infinitum)
  order_classes_ordered : Inf (QualitativeOrder order_classes)

||| The trivial order of the unit type, where the order class type is also unit and the order of the order class type is itself the trivial order
|||
||| This can be used to terminate a finite chain of qualitative orders, where the n'th degree differences are merely partially ordered and not generally qualitatively so.
trivial_order : QualitativeOrder ()
trivial_order =
    MkQualitativeOrder relation
                     reflexive
                     antisymmetric
                     transitive
                     trivial_order
  where
    relation : () -> () -> () -> Type
    relation _ _ _ = ()
    
    reflexive : (y : () ** ((x : ()) -> relation x x y))
    reflexive = (() ** (\_ => ()))

    antisymmetric : (x : ()) -> (y : ()) -> (n : ()) -> (m : ()) -> relation x y n -> relation y x m -> x = y
    antisymmetric () () _ _ _ _ = Refl
    
    transitive : (x : ()) -> (y : ()) -> (z : ()) -> (n : ()) -> (m : ()) -> relation x y n -> relation y z m -> (w : () ** relation x z w)
    transitive _ _ _ _ _ _ _ = (() ** ())
