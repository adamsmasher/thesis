(* lattice stuff influenced by A reflection-based
proof tactic for lattices in Coq by Daniel James
and Ralf Hinze *)

(* also: A Gentle Introducton to Type Classes and
    Relations in Coq by Pierre Casteran *)

Class UpperSemiLattice {A : Set} (join : A -> A -> A) (bottom : A) := {
  join_commutative : forall a b, join a b = join b a;
  join_associatve : forall a b c, join (join a b) c = join a (join b c);
  join_idempotent : forall a, join a a = a;
  bottom_prop : forall a, join bottom a = a
}.