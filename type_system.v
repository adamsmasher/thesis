Require Import target_calculus.

Notation "s → t" := (step s t) (at level 70).
Notation "s →@ t" := (step_ext s t) (at level 70).

Parameter T : Set.
Parameter hasType : term -> T -> Prop.
Parameter lift_label : label -> T.

Axiom subj_red :
  forall e f t, hasType e t -> e →@ f -> hasType f t.

Axiom progress :
  forall e t, hasType e t -> exists f, e → f /\ isValue e.

Axiom labels :
  forall l m, hasType (Label l) (lift_label m) -> precedes l m.

Axiom integers :
  exists int, forall e, isValue e -> (hasType e int <-> exists k, e = Const k).