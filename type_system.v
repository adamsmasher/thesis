(* In this final module, we define the minimum necessary qualities
   a type system (for the target calculus) needs to be able to
   ensure non-interference with our translation. *)

Require Import source_calculus.
Require Import target_calculus.
Require Import translation.
Require Import labels.
Require Import Autosubst.

(* Following Pottier & Conchon, rather than define a particular
   type system, we simply call for a typing predicate defined over
   closed terms of the target calculus and an almost entirely
   abstract set of types that satisfies particular axioms. We encode
   this specification a typeclass. *)

Class TypeSystem
    (type : Type)
    (has_type : term -> type -> Prop)
    (lift_label : label -> type)
    (int : type)
    (pair : type -> type -> type)
:= {
  compositionality : forall e f t,
    is_closed e ->
    is_subexpr e f ->
    has_type f t ->
    exists u, has_type e u;
  subj_red : forall e f t,
    has_type e t -> full_step e f -> has_type f t;
  eta_type : forall e f t,
    has_type e t -> eta_eq e f -> has_type f t;
  progress : forall e t,
    has_type e t -> (exists f, cbn e f) \/ is_value e;
  labels1 : forall l, has_type (Label l) (lift_label l);
  labels2 : forall l m,
    has_type (Label l) (lift_label m) -> precedes l m;
  integers : forall v, has_type v int <-> exists k, v = (Const k);
  pairs1 : forall e f t u,
    has_type (Pair e f) (pair t u) -> has_type e t /\ has_type f u;
  pairs2 : forall e f t u,
    has_type e t -> has_type f u -> exists v, has_type (Pair e f) v
}.

(* For the remainder of this section, we assume we have a valid
   type system and show properties of it. *)
Parameter type : Type.
Parameter has_type : term -> type  -> Prop.
Parameter lift_label : label -> type.
Parameter int : type.
Parameter pair : type -> type -> type.
Parameter TS : TypeSystem type has_type lift_label int pair.

(* Our primary goal is showing that any type system satisfying the
   above axioms can be used to enforce non-interference in the
   source calculus - that is, we can translate a source calculus
   term and the type of the translated term will tell us the labels
   of the data that the term depends on. As per usual, this key
   theorem will require a number of lemmas. *)

(* This lemma extends subject reduction from a single step to
   full sequences. *)
Lemma subj_red_star e f t :
  has_type e t -> star e f -> has_type f t.
Proof.
  induction 2.
  - assumption.
  - apply IHstar. eapply subj_red.
    + apply H.
    + assumption.
Qed.

Lemma source_subj_red e f t :
  has_type (translation e) t -> source_calculus.full_step e f -> has_type (translation f) t.
Proof.
  intros. edestruct (simulation e f) as [u []] ; auto.
  assert (has_type u t) as Hu by eauto using subj_red_star.
  eapply eta_type.
  - apply Hu.
  - assumption.
Qed.

Lemma source_subj_red_star e f t :
  is_term e -> is_term f -> has_type (translation e) t -> source_calculus.star e f -> has_type (translation f) t.
Proof.
  induction 4.
  - assumption.
  - apply IHstar.
    + eauto using term_full_step.
    + assumption.
    + eapply source_subj_red.
        * apply H.
        * eauto using term_full_step.
        * assumption.
        * assumption.
Qed.

Lemma pair_types e f t :
  is_closed e -> is_closed f -> has_type (Pair e f) t -> exists u v, has_type e u /\ has_type f v.
Proof.
  intros.
  destruct (compositionality e (Pair e f) t) ; eauto using is_subexpr.
  destruct (compositionality f (Pair e f) t) ; eauto using is_subexpr.
Qed.

Lemma app_types e f t :
  is_closed e -> is_closed f -> has_type (App e f) t -> exists u v, has_type e u /\ has_type f v.
Proof.
  intros.
  destruct (compositionality e (App e f) t) ; eauto using is_subexpr.
  destruct (compositionality f (App e f) t) ; eauto using is_subexpr.
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

Definition cone (l : label) := fun (m : label) => if precedes_dec m l then true else false.

Inductive label_seq : Type :=
| LabelSeqEmpty
| LabelSeqCons (l : label) (ls : label_seq).

Fixpoint apply_label_seq (ls : label_seq) (e : prefix) : prefix := match ls with
| LabelSeqEmpty => e
| LabelSeqCons l ls => source_calculus.Label (apply_label_seq ls e) l
end.

Fixpoint lift_label_seq (ls : label_seq) : term := match ls with
| LabelSeqEmpty => Label bottom
| LabelSeqCons l ls' => App (App Join (Label l)) (lift_label_seq ls')
end.

Lemma int_value_fst (v : prefix) :
  source_calculus.is_value v -> has_type (eta_fst (translation v)) int -> exists ls k, v = apply_label_seq ls (source_calculus.Const k).
Proof.
  induction v ; intros ; ainv.
  - now exists LabelSeqEmpty, k.
  - simpl in H0. apply integers in H0. ainv.
  - edestruct IHv.
    + assumption.
    + simpl in H0. assumption.
    + destruct H as [k H]. rewrite H. now exists (LabelSeqCons l x), k.
Qed.

Lemma int_trans_fst_type (v : prefix) l :
  source_calculus.is_term v -> source_calculus.is_value v -> has_type (translation v) (pair int l) -> has_type (eta_fst (translation v)) int.
Proof.
  intros. edestruct (translation_pair v).
  - assumption.
  - destruct H2 as [x [H2 _]] ; ainv.
  - destruct H2 as [e1 [e2 H2]]. rewrite H2 in *. simpl. apply pairs1 in H1. tauto.
Qed.

Lemma int_value (v : prefix) l :
  source_calculus.is_term v -> source_calculus.is_value v -> has_type (translation v) (pair int l) -> exists ls k, v = apply_label_seq ls (source_calculus.Const k).
Proof.
  intros. apply int_value_fst.
  - assumption.
  - eapply int_trans_fst_type ; eassumption.
Qed.

Lemma int_value_translation v ls k :
  v = apply_label_seq ls (source_calculus.Const k) -> translation v = Pair (Const k) (lift_label_seq ls).
Proof.
  revert ls. induction v ; intros ; destruct ls ; ainv.
  simpl. now erewrite IHv ; auto.
Qed.

Fixpoint member l ls := match ls with
| LabelSeqEmpty => false
| LabelSeqCons l' ls' => if label_eq l l' then true else member l ls'
end.

Lemma join_label_list ls :
  exists L, (star (lift_label_seq ls) (Label L)) /\ (forall l, member l ls = true -> precedes l L).
Proof.
  induction ls ; simpl.
  - exists bottom. split.
    + eauto using star.
    + inversion 1.
  - destruct IHls as [L [H0 H1]]. exists (join l L). split.
    + eapply star_trans.
       * apply app_star_r. eassumption.
       * apply star_step, FullStep_step. constructor.
    + intros. destruct (label_eq l0 l) ; subst ; ainv.
       * apply semilattice.precedes_join.
       * apply semilattice.precedes_join3. apply H1, H2.
Qed.

Lemma label_list_thing ls L :
  has_type (lift_label_seq ls) (lift_label L) -> forall l, member l ls = true -> precedes l L.
Proof.
  destruct (join_label_list ls) as [L' [H1 H2]]. intro Htype.
  assert (has_type (Label L') (lift_label L)) by eauto using subj_red_star.
  assert (precedes L' L) by auto using labels2.
  intros. apply poset.transitivity with (b := L') ; auto.
Qed.

Lemma filter_list_const L ls k :
  (forall l, member l ls = true -> precedes l L) ->
  label_filter (cone L) (apply_label_seq ls (source_calculus.Const k)) = apply_label_seq ls (source_calculus.Const k).
Proof.
  intros. induction ls ; simpl.
  - reflexivity.
  - assert (precedes l L). { apply H. simpl. destruct (label_eq l l) ; auto. }
    rewrite IHls.
    + unfold cone. destruct (precedes_dec l L) ; simpl.
       * reflexivity.
       * contradiction.
    + intros. apply H. simpl. rewrite H1. destruct (label_eq l0 l) ; auto.
Qed.

Lemma non_interference (e v : source_calculus.prefix) (l : label) :
  is_term e -> has_type (translation e) (pair int (lift_label l)) -> source_calculus.star e v -> source_calculus.is_value v -> source_calculus.star (label_filter (cone l) e) v.
Proof.
  intros. assert (is_term v) by eauto using term_star.
  apply stability ; try assumption.
  assert (has_type (translation v) (pair int (lift_label l))) by eauto using source_subj_red_star.
  assert (exists ls k, v = apply_label_seq ls (source_calculus.Const k)) by eauto using int_value.
  destruct H5 ; destruct H5. rewrite H5.
  apply filter_list_const. apply label_list_thing.
  apply int_value_translation in H5. rewrite H5 in H4.
  apply pairs1 in H4. destruct H4. apply H6.
Qed.
