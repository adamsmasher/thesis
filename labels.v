Require Import poset.
Require Import semilattice.

Section Labels.

(* as in the original paper, we leave the set of labels abstract *)
Parameter label : Set.

(* We want decidability of equality for labels *)
Parameter label_eq : forall (l1 l2 : label), {l1 = l2} + {~l1 = l2}.

(* labels should form a semilattice *)
Parameter precedes : label -> label -> Prop.
Parameter precedes_dec :
  forall l l', {precedes l l'} + {~precedes l l'}.
Parameter bottom : label.
Parameter join : label -> label -> label.
Parameter poset : Poset label precedes.
Parameter semilattice : UpperSemilattice poset join bottom.

(* TODO: move this to poset? *)
Definition cone (l : label) := fun (m : label) =>
  if precedes_dec m l then true else false.

End Labels.

(* Standard join notation. It is placed outside of the section so
   that it can be imported. *)
Notation "l ⋎ m" := (join l m) (at level 70).

(* Cone notation *)
Notation "↓ l" := (cone l) (at level 70).
