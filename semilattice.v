(* lattice stuff influenced by A reflection-based
proof tactic for lattices in Coq by Daniel James
and Ralf Hinze *)

(* also: A Gentle Introducton to Type Classes and
    Relations in Coq by Pierre Casteran *)

Require Import poset.

Class UpperSemiLattice {A} {precedes} (P : Poset A precedes) (join : A -> A -> A) (bottom : A) := {
  join_commutative : forall a b, join a b = join b a;
  join_associative : forall a b c, join (join a b) c = join a (join b c);
  join_idempotent : forall a, join a a = a;
  bottom_prop : forall a, join bottom a = a;
  order_induction : forall a b, precedes a b <-> join a b = b
}.

Lemma precedes_join {A} {precedes} {P : Poset A precedes} {join} {bottom} {USL : UpperSemiLattice P join bottom} a b :
  precedes a (join a b).
Proof.
  apply order_induction. rewrite <- join_associative. now rewrite join_idempotent.
Qed.

Lemma precedes_join2 {A} {precedes} {P : Poset A precedes} {join} {bottom} {USL : UpperSemiLattice P join bottom} a b c :
  precedes a b -> precedes a (join b c).
Proof.
  intros H. assert (join a b = b) as H1 by apply order_induction, H.
  apply order_induction. rewrite <- join_associative. now rewrite H1.
Qed.

Lemma precedes_join3 {A} {precedes} {P : Poset A precedes} {join} {bottom} {USL : UpperSemiLattice P join bottom} a b c :
  precedes a c -> precedes a (join b c).
Proof.
  intros. apply order_induction. rewrite <- join_associative.
  assert (join a b = join b a) as Hab_comm by apply join_commutative.
  rewrite Hab_comm, join_associative.
  assert (join a c = c) as Hac_join by apply order_induction, H.
  now rewrite Hac_join.
Qed.