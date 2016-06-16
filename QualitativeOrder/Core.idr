||| Core definitions for working with qualitative orders
module QualitativeOrder.Core

%default total
%access public export

||| A ternary order relation, relating two elements of one type to some order
||| class in a third type.
Order : (type : Type) -> (order_class : Type) -> Type
Order type order_class = type -> type -> order_class -> Type

||| An infinite sequence of orders, with the type of order classes of one entry
||| being the ordered type of the next
codata OrderStream : (type : Type) -> Type where
  (::) : Order type order_class -> OrderStream order_class -> OrderStream type

||| The reflexive property of an order
|||
||| Orders are reflexive if there is some order class that is related to every
||| element of the ordered type paired with itself.
Reflexive : Order type order_class -> Type
Reflexive {type} {order_class} order = (y : order_class ** ((x : type) -> order x x y))

||| The antisymmetric property of an order
|||
||| Orders are antisymmetric if two elements being relatable in either order
||| implies the elements are equal
Antisymmetric : Order type order_class -> Type
Antisymmetric {type} {order_class} order = (x : type) ->
                                           (y : type) ->
                                           (n : order_class) ->
                                           (m : order_class) ->
                                           order x y n -> order y x m -> x = y

||| The transitive property of an order
|||
||| An order is transitive if x relating to y and y relating to z implies x
||| relates to z in some class
Transitive : Order type order_class -> Type
Transitive {type} {order_class} order = (x : type) ->
                                        (y : type) ->
                                        (z : type) ->
                                        (n : order_class) ->
                                        (m : order_class) ->
                                        order x y n -> order y z m ->
                                        (w : order_class ** order x z w)

||| An order stream is qualitative, i.e. each entry is a partial ordering
|||
||| Called a qualitative order because it's intended to model differences along
||| a single dimension where quantitative relationships are not necessarily
||| available but we still have qualitative differences of degree.
codata Qualitative : OrderStream type -> Type where
  MkQualitative :
    Reflexive order ->
    Antisymmetric order ->
    Transitive order ->
    Qualitative tail ->
    Qualitative (order :: tail)

namespace trivial
  ||| The trivial order orders the unit type with order classes drawn from the
  ||| unit type
  TrivialOrder : Order () ()
  TrivialOrder _ _ _ = ()

  ||| Stream of trivial orders
  TrivialOrderStream : OrderStream ()
  TrivialOrderStream = TrivialOrder :: TrivialOrderStream

  ||| The trivial order stream is qualitative
  |||
  ||| This can be used to terminate a finite qualitative chain whose highest
  ||| order order classes are partially ordered
  TrivialOrderStreamQualitative : Qualitative TrivialOrderStream
  TrivialOrderStreamQualitative =
    MkQualitative (() ** (\_ => ()))
                  (\() => \() => \_ => \_ => \_ => \_ => Refl)
                  (\_ => \_ => \_ => \_ => \_ => \_ => \_ => (() ** ()))
                  TrivialOrderStreamQualitative
