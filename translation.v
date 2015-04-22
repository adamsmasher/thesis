(* This file is where we introduce the translation mechanism used
   to convert between the labelled source calculus and the
   unlabelled target calculus; we also prove a key correctness
   property of it, the simulation property. *)

Require Import source_calculus.
Require Import target_calculus.
Require Import labels.

Require Import Autosubst.

Section Translation.

(* TODO: do we really need to do this again? *)

Instance Ids_prefix : Ids prefix. derive. Defined.
Instance Rename_prefix : Rename prefix. derive. Defined.
Instance Subst_prefix : Subst prefix. derive. Defined.
Instance SubstLemmas_prefix : SubstLemmas prefix. derive. Defined.

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Defined.

(* to keep our lemmas concise, we choose the following
   (admittedly confusing) notations, where a single step arrow
   corresponds to the source calculus single step but the
   reflexive transitive closure arrow is for the target calculus. *)
Notation "s → t" := (source_calculus.full_step s t) (at level 70).
Notation "s →* t" := (target_calculus.star s t) (at level 70).

(* the paper defines translation as a function from source
   calculus terms to pairs of target calculus terms; unfortunately
   we can't do this [due to issues with substitution, expand].
   In particular, variables don't get eta expanded out into
   (fst x, snd x). This has serious ramifications throughout
   the proof that will be discussed as they come up; the first is
   that the paper's definition of translation must be modified
   slightly so as to accomodate the fact that a first and second
   component of a translated term might not exist. The following
   two functions are instead used to destruct a translation; in
   the event that the translation of a term isn't a pair, we
   manually apply the correct destructor. *)

Definition eta_fst (e : target_calculus.term) := match e with
| Pair e1 _ => e1
| _ => App Fst e
end.

Definition eta_snd (e : target_calculus.term) := match e with
| Pair _ e2 => e2
| _ => App Snd e
end.

(* The definition of translation follows. Note that, as mentioned
   above, translations are not guaranteed to be pairs (in the case
   of variables), so we can no longer define it as two
   (mutually recursive) functions.

   The core idea of the translation process, however, is intact:
   source calculus data become pairs in the target calculus,
   with the first component containing the original datum and the
   second component containing the datum's label (using the
   semi-lattice join operation, we discard all but the highest
   label associated with the datum). *)

Fixpoint translation (e : source_calculus.prefix) :
    target_calculus.term :=
  match e with
  | source_calculus.Hole => Pair (Const 0) (Label bottom)
  | source_calculus.Const k => Pair (Const k) (Label bottom)
  | source_calculus.Var x => Var x
  | source_calculus.Abs e => Pair (Abs (translation e)) (Label bottom)
  | source_calculus.App e1 e2 => Pair
     (App Fst (App (eta_fst (translation e1)) (translation e2)))
     ((eta_snd (translation e1)) @
      (App Snd (App (eta_fst (translation e1)) (translation e2))))
  | source_calculus.Let e1 e2 => Pair
      (Let (translation e1) (eta_fst (translation e2)))
      (Let (translation e1) (eta_snd (translation e2)))
  | source_calculus.Label e l => Pair
      (eta_fst (translation e))
      ((Label l) @ (eta_snd (translation e)))
  end.
Notation "⦇ e ⦈" := (translation e).

(* With translation defined, we'd like to show that, in some sense,
   our translated terms correspond to their originals. In
   particular, in order to show non-interference we'll need to
   show that the evaluation relation can be lifted though
   translation - if some source calculus term e evaluates to f
   (in a single step), then the translation of e should evaluate
   (in a sequence of steps) to the translation of f.

   Due to the aforementioned changes to the translation, we
   cannot prove the simulation theorem as stated: we end up with
   situations where we would need two terms - specifically, terms
   of the form (Fst x, Snd x) and x - to be equivalent. Obviously,
   in some useful sense they are, so we encode this property into
   the following inductive predicate, eta_eq. *)

Inductive eta_eq : term -> term -> Prop :=
| EtaEqR s : eta_eq s s
| EtaEqS s t : eta_eq s t -> eta_eq t s
| EtaEqTrans s t u : eta_eq s t -> eta_eq t u -> eta_eq s u
| EtaEqEta s : eta_eq (Pair (App Fst s) (App Snd s)) s
| EtaEqFst s t : eta_eq (App Fst (Pair s t)) s
| EtaEqSnd s t : eta_eq (App Snd (Pair s t)) t
| EtaEqAbs s t : eta_eq s t -> eta_eq (Abs s) (Abs t)
| EtaEqApp s s' t t' :
    eta_eq s s' -> eta_eq t t' -> eta_eq (App s t) (App s' t')
| EtaEqLet s s' t t' :
    eta_eq s s' -> eta_eq t t' -> eta_eq (Let s t) (Let s' t')
| EtaEqPair s s' t t' :
    eta_eq s s' -> eta_eq t t' -> eta_eq (Pair s t) (Pair s' t').

(* The bulk of the remainder of this development consists of various
   lemmas concerning the relationship between eta_fst/eta_snd,
   eta_eq, the step relation, translation, and substitution, all
   ultimately leading to a final proof of the simulation result;
   because neither eta_fst/eta_snd nor eta_eq exist in
   Pottier & Conchon's formulation, and because issues related to
   substitution are generally elided there, little of this
   corresponds to anything in the original paper. *)

(* These lemmas show key relationships between eta_eq and the
   eta_fst and eta_snd functions defined above. *)
Lemma eta_pair x :
  eta_eq (Pair (eta_fst x) (eta_snd x)) x.
Proof.
  induction x ; simpl ; eauto using eta_eq.
Qed.

Lemma eq_app_fst_eta_fst s :
  eta_eq (App Fst s) (eta_fst s).
Proof.
  destruct s ; eauto using eta_eq.
Qed.

Lemma eq_app_snd_eta_snd s :
  eta_eq (App Snd s) (eta_snd s).
Proof.
  destruct s ; eauto using eta_eq.
Qed.

Lemma eta_eq_fst s t :
  eta_eq s t -> eta_eq (eta_fst s) (eta_fst t).
Proof.
  induction 1 ; eauto using eta_eq, eq_app_fst_eta_fst.
Qed.

Lemma eta_eq_snd s t :
  eta_eq s t -> eta_eq (eta_snd s) (eta_snd t).
Proof.
  induction 1 ; eauto using eta_eq, eq_app_snd_eta_snd.
Qed.

(* The following two lemmas show correctness for eta_fst and
   eta_snd, in a sense: when eta_fst or eta_snd is applied to s,
   the result is something (Fst s) or (Snd s) would eventually
   evaluate to. *)

Lemma eta_fst_app s :
  App Fst s →* eta_fst s.
Proof.
  destruct s ; simpl ; try constructor.
  apply star_step, FullStep_step, Step_fst.
Qed.

Lemma eta_snd_app s :
  App Snd s →* eta_snd s.
Proof.
  destruct s ; simpl ; try constructor.
  apply star_step, FullStep_step, Step_snd.
Qed.

(* The following series of lemmas work towards eta_fst_star and
   eta_snd_star, results that show that eta_fst and eta_snd are
   monotonic with respect to the star relation. This fact will
   be used when proving simulation. *)

Lemma eta_fst_step s u :
  target_calculus.step s u -> eta_fst s →* eta_fst u.
Proof.
  destruct 1 ; simpl.
  - eapply star_trans.
    + apply app_star_r. apply star_step, FullStep_step, Step_beta.
    + apply eta_fst_app.
  - eapply star_trans.
    + apply app_star_r. apply star_step, FullStep_step, Step_let.
    + apply eta_fst_app.
  - eapply star_trans.
    + apply app_star_r. apply star_step, FullStep_step, Step_fst.
    + apply eta_fst_app.
  - eapply star_trans.
    + apply app_star_r. apply star_step, FullStep_step, Step_snd.
    + apply eta_fst_app.
  - apply app_star_r. apply star_step, FullStep_step, Step_join.
  - apply app_star_r. apply star_step, FullStep_step, Step_assoc.
  - eapply star_trans.
    + apply app_star_r. apply star_step, FullStep_step, Step_neutral.
    + apply eta_fst_app.
Qed.

Lemma eta_fst_full_step s u :
  target_calculus.full_step s u -> eta_fst s →* eta_fst u.
Proof.
  destruct 1 ; simpl.
  - now apply eta_fst_step.
  - apply app_star_r. apply abs_star. now apply star_step.
  - apply app_star_r. apply app_star_l. now apply star_step.
  - apply app_star_r. apply app_star_r. now apply star_step.
  - apply app_star_r. apply let_star_l. now apply star_step.
  - apply app_star_r. apply let_star_r. now apply star_step.
  - now apply star_step.
  - constructor.
Qed.

Lemma eta_snd_step s u :
  target_calculus.step s u -> eta_snd s →* eta_snd u.
Proof.
  destruct 1 ; simpl.
  - eapply star_trans.
    + apply app_star_r. apply star_step, FullStep_step, Step_beta.
    + apply eta_snd_app.
  - eapply star_trans.
    + apply app_star_r. apply star_step, FullStep_step, Step_let.
    + apply eta_snd_app.
  - eapply star_trans.
    + apply app_star_r. apply star_step, FullStep_step, Step_fst.
    + apply eta_snd_app.
  - eapply star_trans.
    + apply app_star_r. apply star_step, FullStep_step, Step_snd.
    + apply eta_snd_app.
  - apply app_star_r. apply star_step, FullStep_step, Step_join.
  - apply app_star_r. apply star_step, FullStep_step, Step_assoc.
  - eapply star_trans.
    + apply app_star_r. apply star_step, FullStep_step, Step_neutral.
    + apply eta_snd_app.
Qed.

Lemma eta_snd_full_step s u :
  target_calculus.full_step s u -> eta_snd s →* eta_snd u.
Proof.
  destruct 1 ; simpl.
  - now apply eta_snd_step.
  - apply app_star_r. apply abs_star. now apply star_step.
  - apply app_star_r. apply app_star_l. now apply star_step.
  - apply app_star_r. apply app_star_r. now apply star_step.
  - apply app_star_r. apply let_star_l. now apply star_step.
  - apply app_star_r. apply let_star_r. now apply star_step.
  - constructor.
  - now apply star_step.
Qed.

Lemma eta_fst_star s u :
  s →* u -> eta_fst s →* eta_fst u.
Proof.
  induction 1.
  - constructor.
  - apply eta_fst_full_step in H. eapply star_trans ; eauto.
Qed.

Lemma eta_snd_star s u :
  s →* u -> eta_snd s →* eta_snd u.
Proof.
  induction 1.
  - constructor.
  - apply eta_snd_full_step in H. eapply star_trans ; eauto.
Qed.

Lemma fst_ren s xi :
  ⦇s⦈.[ren xi] = ⦇s.[ren xi]⦈ ->
  (eta_fst ⦇s⦈).[ren xi] = eta_fst ⦇s.[ren xi]⦈.
Proof.
  destruct s ; simpl ; ainv.
Qed.

Lemma snd_ren s xi :
  ⦇s⦈.[ren xi] = ⦇s.[ren xi]⦈ ->
  (eta_snd ⦇s⦈).[ren xi] = eta_snd ⦇s.[ren xi]⦈.
Proof.
  destruct s ; simpl ; ainv.
Qed.

Lemma ren_translation xi : translation >>> (subst (xi >>> ids)) = subst (xi >>> ids) >>> translation.
Proof.
  f_ext. intros s. simpl. revert xi. induction s ; intros ; asimpl ; autosubst_unfold ; try now autorew ;
  repeat f_equal ; eauto using fst_ren, snd_ren.
Qed.

Hint Rewrite @ren_translation : autosubst.

Lemma ren_up sigma :
    up sigma >>> translation = up (sigma >>> translation).
Proof. autosubst. Qed.

Lemma five_one e sigma (H1 : is_term e) :
   ⦇e⦈.[sigma >>> translation] →* ⦇e.[sigma]⦈ /\ (eta_fst ⦇e⦈).[sigma >>> translation] →* eta_fst ⦇e.[sigma]⦈ /\ (eta_snd ⦇e⦈).[sigma >>> translation] →* eta_snd ⦇e.[sigma]⦈.
Proof.
  revert sigma. induction e ; intros ; simpl ; eauto using step, star ; inversion H1 ; subst ; repeat split.
  - constructor.
  - destruct (sigma x) ; eauto using star, full_step, step.
  - destruct (sigma x) ; eauto using star, full_step, step.
  - apply pair_star_l. rewrite <- ren_up. apply abs_star. now apply IHe.
  - rewrite <- ren_up. apply abs_star. now apply IHe.
  - constructor.
  - apply pair_star.
    + apply app_star_r. apply app_star.
       * now apply IHe1.
       * now apply IHe2.
    + apply app_star.
       * apply app_star_r. now apply IHe1.
       * apply app_star_r. apply app_star.
          { now apply IHe1. }
          { now apply IHe2. }
  - apply app_star_r. apply app_star.
     + now apply IHe1.
     + now apply IHe2.
  - apply app_star.
     + apply app_star_r. now apply IHe1.
     + apply app_star_r. apply app_star.
        * now apply IHe1.
        * now apply IHe2.
  - apply pair_star.
    + apply let_star.
       * now apply IHe.
       * rewrite <- ren_up. now apply IHe0.
    + apply let_star.
       * now apply IHe.
       * rewrite <- ren_up. now apply IHe0.
  - apply let_star.
    + now apply IHe.
    + rewrite <- ren_up. now apply IHe0.
  - apply let_star.
    + now apply IHe.
    + rewrite <- ren_up. now apply IHe0.
  - apply pair_star.
    + now apply IHe.
    + apply app_star_r. now apply IHe.
  - now apply IHe.
  - apply app_star_r. now apply IHe.
Qed.

Lemma five_one' e1 e2 (H1 : is_term e1) (H2 : is_term e2) :
  ⦇e1⦈.[⦇e2⦈/] →* ⦇e1.[e2/]⦈ /\ (eta_fst ⦇e1⦈).[⦇e2⦈/] →* eta_fst ⦇e1.[e2/]⦈ /\ (eta_snd ⦇e1⦈).[⦇e2⦈/] →* eta_snd ⦇e1.[e2/]⦈.
Proof.
  repeat split.
  - assert (exists sigma, ⦇e1⦈.[scons (translation e2) ids] = ⦇e1⦈.[sigma >>> translation] /\ ⦇e1.[scons e2 ids]⦈ = ⦇e1.[sigma]⦈).
    { unfold ids. unfold Ids_term. unfold funcomp. unfold scons.
      exists (fun x => match x with 0 => e2 | S y => source_calculus.Var y end).
      split ; auto. repeat f_equal ; f_ext ; intros ; destruct x ; auto.
    }
    destruct H as [sigma [HL HR]]. autorew. now apply five_one.
  - assert (exists sigma, (eta_fst ⦇e1⦈).[scons (translation e2) ids] = (eta_fst ⦇e1⦈).[sigma >>> translation] /\ eta_fst ⦇e1.[scons e2 ids]⦈ = eta_fst ⦇e1.[sigma]⦈).
    { unfold ids. unfold Ids_term. unfold funcomp. unfold scons.
      exists (fun x => match x with 0 => e2 | S y => source_calculus.Var y end).
      split ; auto. repeat f_equal ; f_ext ; intros ; destruct x ; auto.
    }
    destruct H as [sigma [HL HR]]. autorew. now apply five_one.
  - assert (exists sigma, (eta_snd ⦇e1⦈).[scons (translation e2) ids] = (eta_snd ⦇e1⦈).[sigma >>> translation] /\ eta_snd ⦇e1.[scons e2 ids]⦈ = eta_snd ⦇e1.[sigma]⦈).
    { unfold ids. unfold Ids_term. unfold funcomp. unfold scons.
      exists (fun x => match x with 0 => e2 | S y => source_calculus.Var y end).
      split ; auto. repeat f_equal ; f_ext ; intros ; destruct x ; auto.
    }
    destruct H as [sigma [HL HR]]. autorew. now apply five_one.
Qed.

(* To simplify the proof of simuation, we've split it up into
   separate lemmas for each case of the step relation. *)

Lemma simulation_beta s t :
  is_term s ->
  is_term t ->
  exists u,
  ⦇source_calculus.App (source_calculus.Abs s) t⦈ →* u /\
  eta_eq u ⦇s.[t/]⦈.
Proof.
  simpl. repeat esplit.
  - eapply star_trans.
    + apply pair_star.
      * apply app_star_r. apply star_step, FullStep_step, Step_beta.
      * apply star_step, FullStep_step, Step_neutral.
    + eapply star_trans.
       * apply pair_star.
         { apply app_star_r. now apply five_one'. }
         { apply app_star_r. apply star_step, FullStep_step, Step_beta. }
       * apply pair_star_r. apply app_star_r. now apply five_one'.
  - apply EtaEqEta.
Qed.

Lemma simulation_let s t :
  is_term s ->
  is_term t ->
  exists u,
  ⦇source_calculus.Let s t⦈ →* u /\
  eta_eq u ⦇t.[s/]⦈.
Proof.
  simpl. repeat esplit.
  - eapply star_trans.
    + apply pair_star ; apply star_step, FullStep_step, Step_let.
    + apply pair_star ; now apply five_one'.
  - apply eta_pair.
Qed.

Lemma simulation_label s l t :
  exists u,
  ⦇source_calculus.App (source_calculus.Label s l ) t⦈ →* u  /\
  eta_eq u ⦇source_calculus.Label (source_calculus.App s t) l⦈.
Proof.
  intros. simpl. repeat esplit.
  - apply pair_star_r, star_step, FullStep_step, Step_assoc.
  - constructor.
Qed.

Lemma simulation_step (e f : source_calculus.prefix) :
  is_term e ->
  is_term f ->
  source_calculus.step e f ->
  exists u, ⦇e⦈ →* u /\ eta_eq u ⦇f⦈.
Proof.
  destruct 3 ; ainv.
  - now apply simulation_beta.
  - now apply simulation_let.
  - now apply simulation_label.
Qed.

Lemma simulation (e f : source_calculus.prefix) :
  is_term e ->
  is_term f ->
  e → f ->
  exists u, ⦇e⦈  →* u /\ eta_eq u ⦇f⦈.
Proof.
  induction 3 ; ainv ; simpl.
  - now apply simulation_step.
  - destruct IHfull_step as [x []]; auto. repeat esplit.
    + apply pair_star_l, abs_star. eassumption.
    + eauto using eta_eq.
  - destruct IHfull_step as [x []]; auto. repeat esplit.
    + apply pair_star.
       * apply app_star_r, app_star_l. apply eta_fst_star. eassumption.
       * apply app_star.
          { apply app_star_r. apply eta_snd_star. eassumption. }
          { apply app_star_r, app_star_l. apply eta_fst_star. eassumption. }
    + apply EtaEqPair ; eauto 7 using eta_eq, eta_eq_fst, eta_eq_snd.
  - destruct IHfull_step as [x []]; auto. repeat esplit. apply pair_star.
    + apply app_star_r, app_star_r. eassumption.
    + apply app_star_r, app_star_r, app_star_r. eassumption.
    + apply EtaEqPair ; eauto using eta_eq.
  - destruct IHfull_step as [x []] ; auto. repeat esplit.
    + apply pair_star ; apply let_star_l ; eassumption.
    + apply EtaEqPair ; eauto using eta_eq.
  - destruct IHfull_step as [x []] ; auto. repeat esplit.
    + apply pair_star.
       * apply let_star_r. apply eta_fst_star. eassumption.
       * apply let_star_r. apply eta_snd_star. eassumption.
    + apply EtaEqPair ; eauto using eta_eq, eta_eq_fst, eta_eq_snd.
  - destruct IHfull_step as [x []] ; auto. repeat esplit.
    + apply pair_star.
       * apply eta_fst_star. eassumption.
       * apply app_star_r. apply eta_snd_star. eassumption.
    + apply EtaEqPair ; eauto using eta_eq, eta_eq_fst, eta_eq_snd.
Qed.

(*
Lemma translation_pair e :
  is_term e -> (exists x, e = source_calculus.Var x /\ translation e = Var x) \/ (exists e1 e2, translation e = Pair e1 e2).
Proof.
  intros. destruct e ; simpl.
  - inversion H.
  - right. eauto.
  - left. eauto.
  - right. eauto.
  - right. eauto.
  - right. eauto.
  - right. eauto.
Qed.

Lemma translation_closed_fst e n :
  n_closed n e -> n_closed n (eta_fst e).
Proof.
  intros. destruct e ; simpl.
  - repeat constructor.
  - constructor.
    + constructor.
    + assumption.
  - inversion H ; subst. repeat constructor ; auto.
  - inversion H ; subst. repeat constructor ; auto.
  - inversion H ; subst. repeat constructor ; auto.
  - inversion H ; subst. auto.
  - repeat constructor.
  - repeat constructor.
  - repeat constructor.
  - repeat constructor.
Qed.

Lemma translation_closed_snd e n :
  n_closed n e -> n_closed n (eta_snd e).
Proof.
  intros. destruct e ; simpl.
  - repeat constructor.
  - constructor.
    + constructor.
    + assumption.
  - inversion H ; subst. repeat constructor ; auto.
  - inversion H ; subst. repeat constructor ; auto.
  - inversion H ; subst. repeat constructor ; auto.
  - inversion H ; subst. auto.
  - repeat constructor.
  - repeat constructor.
  - repeat constructor.
  - repeat constructor.
Qed.

Lemma translation_closed e n :
  source_calculus.n_closed n e -> n_closed n (translation e).
Proof.
  revert n. induction e ; simpl ; intros.
  - repeat constructor.
  - repeat constructor.
  - constructor. ainv.
  - ainv. constructor.
    + constructor. now apply IHe.
    + constructor.
  - ainv. repeat constructor.
    + apply translation_closed_fst. now apply IHe1.
    + now apply IHe2.
    + apply translation_closed_snd. now apply IHe1.
    + apply translation_closed_fst. now apply IHe1.
    + now apply IHe2.
  - ainv. repeat constructor.
    + now apply IHe.
    + apply translation_closed_fst. now apply IHe0.
    + now apply IHe.
    + apply translation_closed_snd. now apply IHe0.
  - ainv. repeat constructor.
    + apply translation_closed_fst. now apply IHe.
    + apply translation_closed_snd. now apply IHe.
Qed.*)

End Translation.
