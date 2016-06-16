||| Core definitions for working with qualitative orders
module QualitativeOrder.Core

%default total
%access public export

||| A (partial) ordering of a type with infinitely deep higher order ordering
|||
||| Called a qualitative order because it's intended to model differences along a single dimension where quantitative relationships are unavailable but we still have qualitative differences of degree.
||| @ type The type being ordered
||| @ order The order relation
||| @ order_classes The type of order classes
data QualitativeOrder : (type : Type) -> (order : type -> type -> order_classes -> Type) -> Type where
  ||| Make a qualitative order
  ||| @ reflexive `order` is reflexive
  ||| @ antisymmetric `order` is antisymmetric
  ||| @ transitive `order` is transitive
  ||| @ order_classes_ordered The type of order classes is itself qualitatively ordered
  MkQualitativeOrder :
    (reflexive : (y : order_classes ** ((x : type) -> (order x x y)))) ->
    (antisymmetric : ((x : type) -> (y : type) -> (n : order_classes) -> (m : order_classes) -> (order x y n) -> (order y x m) -> x = y)) ->
    (transitive : ((x : type) -> (y : type) -> (z : type) -> (n : order_classes) -> (m : order_classes) -> (order x y n) -> (order y z m) -> (w : order_classes ** order x z w))) ->
    (order_classes_ordered : Inf (QualitativeOrder order_classes order_classes_order)) ->
    QualitativeOrder type order

||| The trivial order of the unit type, where the order class type is also unit and the order of the order class type is itself the trivial order
|||
||| This can be used to terminate a finite chain of qualitative orders, where the n'th degree differences are merely partially ordered and not generally qualitatively so.
TrivialOrder : QualitativeOrder {order_classes=()} () (\_ => \_ => \_ => ())
TrivialOrder =
    MkQualitativeOrder (() ** (\_ => ()))
                       (\() => \() => \_ => \_ => \_ => \_ => Refl)
                       (\_ => \_ => \_ => \_ => \_ => \_ => \_ => (() ** ()))
                       TrivialOrder
