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

Lemma eta_fst_trans e t (Hterm : is_term e) (Hclosed : source_calculus.is_closed e) :
  has_type (translation e) t -> exists u, has_type (eta_fst (translation e)) u.
Proof.
  induction e ; simpl ; intros.
  - inversion Hterm.
  - exists int. apply integers ; eauto.
  - inversion Hclosed. ainv.
  - ainv. apply pair_types in H.
    + repeat destruct H. eauto.
    + constructor ; auto using translation_closed.
    + constructor.
  - ainv. apply pair_types in H.
    + repeat destruct H. eauto.
    + repeat constructor ; auto using translation_closed, translation_closed_fst.
    + repeat constructor ; auto using translation_closed, translation_closed_fst, translation_closed_snd.
  - ainv. apply pair_types in H.
    + repeat destruct H. eauto.
    + repeat constructor ; auto using translation_closed, translation_closed_fst.
    + repeat constructor ; auto using translation_closed, translation_closed_snd.
  - ainv. apply pair_types in H.
    + repeat destruct H. eauto.
    + now apply translation_closed_fst, translation_closed.
    + repeat constructor. now apply translation_closed_snd, translation_closed.
Qed.

Lemma translate_etas e t u (Hterm : is_term e) (Hclosed : source_calculus.is_closed e) :
  has_type (eta_fst (translation e)) t -> has_type (eta_snd (translation e)) u -> exists v, has_type (translation e) v.
Proof.
  induction e ; simpl ; intros.
  - inversion Hterm.
  - eapply pairs2.
    + eassumption.
    + apply labels1.
  - inversion Hclosed ; ainv.
  - eapply pairs2 ; eauto using labels1.
  - eapply pairs2 ; eauto.
  - eapply pairs2 ; eauto.
  - eapply pairs2 ; eauto.
Qed.

Inductive appliable : prefix -> Prop :=
| AppliableAbs s : appliable (source_calculus.Abs s)
| AppliableLift s l : appliable s -> appliable (source_calculus.Label s l).

Lemma translation_appliable s t u :
  is_term s -> cbn (App (eta_fst (translation s)) t) u -> source_calculus.is_value s -> appliable s.
Proof.
  intros. induction s ; ainv.
  - inversion H0 ; ainv.
  - constructor.
  - constructor. apply IHs ; auto.
Qed.

Lemma appliable_exist_cbn s t :
  appliable s -> exists u, source_calculus.cbn (source_calculus.App s t) u.
Proof.
  intros. induction H ; eauto using source_calculus.cbn, source_calculus.step.
Qed.

Lemma app_translation_reducible e1 e2 :
  ~is_value (App (eta_fst (translation e1)) (translation e2)).
Proof.
  intro. induction e1 ; ainv. apply IHe1. rewrite <- H1.  rewrite <- H0. constructor.
Qed.

Lemma source_progress e t (Hterm : is_term e) (Hclosed : source_calculus.is_closed e) :
  has_type (translation e) t -> (exists f, source_calculus.cbn e f) \/ source_calculus.is_value e.
Proof.
  revert t. induction e ; simpl ; intros.
  - inversion Hterm.
  - right. constructor.
  - inversion Hclosed ; ainv.
  - right. constructor.
  - ainv.
    apply pair_types in H. repeat destruct H. apply app_types in H. repeat destruct H.
    apply app_types in H1. repeat destruct H1. apply app_types in H0. repeat destruct H0.
    apply app_types in H0. repeat destruct H0.
    + assert (exists u, has_type (translation e1) u) by eauto using translate_etas.
       destruct H9. edestruct IHe1 ; eauto.
       * destruct H10. left. eauto using source_calculus.cbn.
       * apply app_types in H7. repeat destruct H7. apply progress in H11. destruct H11.
       { destruct H11. left. apply appliable_exist_cbn. eapply translation_appliable ; eauto. }
       { exfalso. eapply app_translation_reducible ; eassumption. }
       { constructor. }
       { constructor ; auto using translation_closed_fst, translation_closed. }
    + constructor.
    + now apply translation_closed_snd, translation_closed.
    + constructor.
       * constructor.
       * now apply translation_closed_snd, translation_closed.
    + constructor.
       * constructor.
       * constructor ; auto using translation_closed_fst, translation_closed.
    + now apply translation_closed_fst, translation_closed.
    + now apply translation_closed.
    + constructor.
    + constructor ; auto using translation_closed_fst, translation_closed.
    + constructor.
        * constructor.
        * constructor ; auto using translation_closed_fst, translation_closed.
    + constructor ; auto using translation_closed_fst, translation_closed_snd, translation_closed, n_closed.
  - left. esplit. repeat constructor.
  - ainv.
    apply pair_types in H. repeat destruct H. apply app_types in H0. repeat destruct H0.
    + assert (exists u, has_type (translation e) u) by eauto using translate_etas.
       destruct H4. edestruct IHe ; eauto.
       * destruct H5. left. eauto using source_calculus.cbn.
       * right. now constructor.
    + repeat constructor.
    + now apply translation_closed_snd, translation_closed.
    + now apply translation_closed_fst, translation_closed.
    + repeat constructor. now apply translation_closed_snd, translation_closed.
Qed.