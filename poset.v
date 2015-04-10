(* A typeclass representing a partially ordered set (Poset). Needed
   as we require the set of labels to be an upper semilattice
   (which is a poset with additional properties). *)

(* TODO: [cite], talk about why we use typeclasses *)

Class Poset (A : Set) (precedes : A -> A -> Prop) := {
  reflexivity : forall a, precedes a a;
  antisymmetry : forall a b, precedes a b -> precedes b a -> a = b;
  transitivity : forall a b c, precedes a b -> precedes b c -> precedes a c
}.