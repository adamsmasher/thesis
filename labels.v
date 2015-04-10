Require Import poset.
Require Import semilattice.

Section Labels.

(* as in the original paper, for now we leave
     the set of labels entirely abstract *)

Parameter label : Set.

(* We want decidability of equality for labels *)

Parameter label_eq : forall (l1 l2 : label), {l1 = l2} + {~l1 = l2}.

(* labels should form a semi-lattice *)

Parameter precedes : label -> label -> Prop.
Parameter precedes_dec : forall l l', {precedes l l'} + {~precedes l l'}.
Parameter bottom : label.
Parameter join : label -> label -> label.
Parameter poset : Poset label precedes.
Parameter semilattice : UpperSemilattice poset join bottom.

End Labels.