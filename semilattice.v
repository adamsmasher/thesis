(* lattice stuff influenced by A reflection-based
proof tactic for lattices in Coq by Daniel James
and Ralf Hinze *)

(* also: A Gentle Introducton to Type Classes and
    Relations in Coq by Pierre Casteran *)

Require Import poset.

Class UpperSemiLattice {A} {precedes} (P : Poset A precedes) (join : A -> A -> A) (bottom : A) := {
  join_commutative : forall a b, join a b = join b a;
  join_associatve : forall a b c, join (join a b) c = join a (join b c);
  join_idempotent : forall a, join a a = a;
  bottom_prop : forall a, join bottom a = a;
  order_induction : forall a b, precedes a b <-> join a b = b
}.