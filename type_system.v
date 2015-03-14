Require Import source_calculus.
Require Import target_calculus.
Require Import translation.
Require Import Autosubst.

Class TypeSystem
    (type : Type)
    (has_type : term -> type -> Prop)
    (lift_label : label -> type)
    (int : type)
    (pair : type -> type -> type)
:= {
  compositionality : forall e f t, is_closed e -> is_subexpr e f -> has_type f t -> exists u, has_type e u;
  subj_red : forall e f t, has_type e t -> full_step e f -> has_type f t;
  eta_type : forall e f t, has_type e t -> eta_eq e f -> has_type f t;
  progress : forall e t, has_type e t -> (exists f, cbn e f) \/ is_value e;
  labels1 : forall l, has_type (Label l) (lift_label l);
  labels2 : forall l m, has_type (Label l) (lift_label m) -> precedes l m;
  integers : forall v, has_type v int <-> exists k, v = (Const k);
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
  intros. induction H0.
  - assumption.
  - apply IHstar. eapply subj_red.
    + apply H.
    + assumption.
Qed.

Lemma source_subj_red e f t :
  is_term e -> is_term f -> has_type (translation e) t -> source_calculus.full_step e f -> has_type (translation f) t.
Proof.
  intros. edestruct (simulation e f) as [u []] ; auto.
  assert (has_type u t) as Hu by eauto using subj_red_star.
  eapply eta_type.
  - apply Hu.
  - assumption.
Qed.

Lemma pair_types e f t :
  is_closed e -> is_closed f -> has_type (Pair e f) t -> exists u v, has_type e u /\ has_type f v.
Proof.
  intros.
  destruct (compositionality e (Pair e f) t) ; auto using is_subexpr.
  destruct (compositionality f (Pair e f) t) ; auto using is_subexpr.
  eauto.
Qed.

Lemma app_types e f t :
  is_closed e -> is_closed f -> has_type (App e f) t -> exists u v, has_type e u /\ has_type f v.
Proof.
  intros.
  destruct (compositionality e (App e f) t) ; auto using is_subexpr.
  destruct (compositionality f (App e f) t) ; auto using is_subexpr.
  eauto.
Qed.

(*
Lemma translate_abs e t (H : is_term e) :
  has_type (translation (source_calculus.Abs e)) t -> exists u, has_type (translation e) u.
Proof.
  simpl ; intros. edestruct pair_types as [u [v []]].
  - eassumption.
  - edestruct abs_types ; eauto.
Qed.

Lemma eta_fst_trans e t (H : is_term e) :
  has_type (translation e) t -> exists u, has_type (eta_fst (translation e)) u.
Proof.
  revert t. induction e ; simpl ; intros.
  - inversion H.
  - exists int. apply integers ; eauto.
  - admit. (* closed *)
  - destruct (pair_types _ _ _ H0) as [u [v []]] ; eauto.
  - destruct (pair_types _ _ _ H0) as [u [v []]] ; eauto.
  - destruct (pair_types _ _ _ H0) as [u [v []]] ; eauto.
  - destruct (pair_types _ _ _ H0) as [u [v []]] ; eauto.
Admitted.

Lemma eta_snd_trans e t (H : is_term e) :
  has_type (translation e) t -> exists u, has_type (eta_snd (translation e)) u.
Proof.
  revert t. induction e ; simpl ; intros.
  - inversion H.
  - exists (lift_label bottom). apply labels1.
  - admit. (* TODO: closed *)
  - destruct (pair_types _ _ _ H0) as [u [v []]] ; eauto.
  - destruct (pair_types _ _ _ H0) as [u [v []]] ; eauto.
  - destruct (pair_types _ _ _ H0) as [u [v []]] ; eauto.
  - destruct (pair_types _ _ _ H0) as [u [v []]] ; eauto.
Admitted.

Lemma translate_eta_fst e t (H : is_term e) :
  has_type (eta_fst (translation e)) t -> exists u, has_type (translation e) u.
Proof.
  revert t. induction e ; simpl ; intros.
  - inversion H.
  - eapply pairs2.
    + eassumption.
    + apply labels1.
  - admit. (* TODO: closed *)
  - inversion H ; subst. edestruct abs_types ; eauto. edestruct eta_fst_trans ; eauto. edestruct IHe ; eauto.
    eapply pairs2 ; eauto using labels1.
  - inversion H ; subst. edestruct app_types as [u [v [H1 H2]]] ; eauto. destruct (app_types _ _ _ H2) as [u' [v' []]].
    edestruct IHe1 ; eauto. admit.
  - inversion H ; subst. admit.
  - eapply pairs2 ; eauto.
Admitted.
*)
Lemma source_progress e t (H : is_term e) :
  has_type (translation e) t -> (exists f, cbn (translation e) f) \/ is_value (translation e).
Proof.
  revert t. induction e ; simpl ; intros.
  - inversion H.
  - right. constructor.
  - left. apply progress in H0. destruct H0.
    + assumption.
    + inversion H0.
  - right. constructor.
  - left. inversion H ; subst. admit.
  - admit.
  - admit.
Admitted.