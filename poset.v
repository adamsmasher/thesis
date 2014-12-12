Class Poset (A : Set) (precedes : A -> A -> Prop) := {
  reflexivity : forall a, precedes a a;
  antisymmetry : forall a b, precedes a b -> precedes b a -> a = b;
  transitivity : forall a b c, precedes a b -> precedes b c -> precedes a c
}.