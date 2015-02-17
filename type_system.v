Require Import source_calculus.
Require Import target_calculus.
Require Import translation.

Class TypeSystem
    (type : Type)
    (has_type : term -> type -> Prop)
    (lift_label : label -> type)
    (int : type)
    (pair : type -> type -> type)
:= {
  compositionality : forall e f t, is_subexpr e f -> has_type f t -> exists u, has_type e u;
  subj_red : forall e f t, has_type e t -> full_step e f -> has_type f t;
  progress : forall e t, has_type e t -> (exists f, cbn e f) \/ is_value e;
  labels : forall l m, has_type (Label l) (lift_label m) -> precedes l m;
  integers : forall v, has_type v int <-> exists k, v = Const k;
  pairs1 : forall e f t u, has_type (Pair e f) (pair t u) -> has_type e t /\ has_type f u;
  pairs2 : forall e f t u, has_type e t -> has_type f u -> exists v, has_type (Pair e f) v
}.

Parameter type : Type.
Parameter has_type : term -> type  -> Prop.
Parameter lift_label : label -> type.
Parameter int : type.
Parameter pair : type -> type -> type.
Parameter TS : TypeSystem type has_type lift_label int pair.

Lemma subj_red_star e f t :
  has_type e t -> star e f -> has_type f t.
Proof.
  induction 2.
  - assumption.
  - apply IHstar. eapply subj_red ; eassumption.
Qed.

Lemma source_subj_red e f t :
  is_term e -> is_term f -> has_type (translation e) t -> source_calculus.full_step e f -> exists u, eta_eq u (translation f) /\ has_type u t.
Proof.
  intros. edestruct (simulation e f) as [u []] ; auto. exists u. split.
  - assumption.
  - eapply subj_red_star ; eassumption.
Qed.