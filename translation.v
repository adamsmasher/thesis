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
   (somewhat confusing) notations, where a single step arrow
   corresponds to the source calculus single step but the
   reflexive transitive closure arrow is for the target calculus. *)
Notation "s → t" := (source_calculus.full_step s t) (at level 70).
Notation "s →* t" := (target_calculus.star s t) (at level 70).

Definition eta_fst (e : target_calculus.term) := match e with
| Pair e1 _ => e1
| _ => App Fst e
end.

Definition eta_snd (e : target_calculus.term) := match e with
| Pair _ e2 => e2
| _ => App Snd e
end.

Fixpoint translation (e : source_calculus.prefix) : target_calculus.term :=
  match e with
  | source_calculus.Hole => Pair (Const 0) (Label bottom)
  | source_calculus.Const k => Pair (Const k) (Label bottom)
  | source_calculus.Var x => Var x
  | source_calculus.Abs e => Pair (Abs (translation e)) (Label bottom)
  | source_calculus.App e1 e2 => Pair
     (App Fst (App (eta_fst (translation e1)) (translation e2)))
     ((eta_snd (translation e1)) @ (App Snd (App (eta_fst (translation e1)) (translation e2))))
  | source_calculus.Let e1 e2 => Pair
      (Let (translation e1) (eta_fst (translation e2)))
      (Let (translation e1) (eta_snd (translation e2)))
  | source_calculus.Label e l => Pair
      (eta_fst (translation e))
      ((Label l) @ (eta_snd (translation e)))
  end.
Notation "⦇ e ⦈" := (translation e).


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
Qed.

Inductive eta_eq : term -> term -> Prop :=
| EtaEqR s : eta_eq s s
| EtaEqS s t : eta_eq s t -> eta_eq t s
| EtaEqTrans s t u : eta_eq s t -> eta_eq t u -> eta_eq s u
| EtaEqEta s : eta_eq (Pair (App Fst s) (App Snd s)) s
| EtaEqFst s t : eta_eq (App Fst (Pair s t)) s
| EtaEqSnd s t : eta_eq (App Snd (Pair s t)) t
| EtaEqAbs s t : eta_eq s t -> eta_eq (Abs s) (Abs t)
| EtaEqApp s s' t t' : eta_eq s s' -> eta_eq t t' -> eta_eq (App s t) (App s' t')
| EtaEqLet s s' t t' : eta_eq s s' -> eta_eq t t' -> eta_eq (Let s t) (Let s' t')
| EtaEqPair s s' t t' : eta_eq s s' -> eta_eq t t' -> eta_eq (Pair s t) (Pair s' t').





Lemma fst_ren s xi :
  ⦇s⦈.[ren xi] = ⦇s.[ren xi]⦈ -> (eta_fst ⦇s⦈).[ren xi] = eta_fst ⦇s.[ren xi]⦈.
Proof.
  revert xi. destruct s ; intros xi H ; try autosubst ; simpl ; inversion H ; f_equal.
Qed.

Lemma snd_ren s xi :
  ⦇s⦈.[ren xi] = ⦇s.[ren xi]⦈ -> (eta_snd ⦇s⦈).[ren xi] = eta_snd ⦇s.[ren xi]⦈.
Proof.
  revert xi. destruct s ; intros xi H ; try autosubst ; simpl ; inversion H ; f_equal.
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

Lemma eta_pair x :
  eta_eq (Pair (eta_fst x) (eta_snd x)) x.
Proof.
  induction x ; simpl ; eauto using eta_eq.
Qed.

Lemma simulation_beta s t (H : is_term (source_calculus.App (source_calculus.Abs s) t)) :
  exists u, ⦇source_calculus.App (source_calculus.Abs s) t⦈ →* u /\ eta_eq u ⦇s.[t/]⦈.
Proof.
  ainv. simpl. esplit. split.
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

Lemma simulation_let s t (H : is_term (source_calculus.Let s t)) :
  exists u, ( ⦇source_calculus.Let s t⦈ →* u /\ eta_eq u ⦇t.[s/]⦈).
Proof.
  ainv. simpl. esplit. split.
  - eapply star_trans.
    + apply pair_star ; apply star_step, FullStep_step, Step_let.
    + apply pair_star ; now apply five_one'.
  - apply eta_pair.
Qed.

Lemma simulation_label s l t (H : is_term (source_calculus.App (source_calculus.Label s l) t)) :
  exists u, ⦇source_calculus.App (source_calculus.Label s l ) t⦈ →* u  /\ eta_eq u ⦇source_calculus.Label (source_calculus.App s t) l⦈.
Proof.
  ainv. simpl. repeat esplit.
  - apply pair_star_r, star_step, FullStep_step, Step_assoc.
  - constructor.
Qed.

Lemma simulation_step (e f : source_calculus.prefix) (He : is_term e) (Hf : is_term f) :
  source_calculus.step e f  -> exists u, ⦇e⦈ →* u /\ eta_eq u ⦇f⦈.
Proof.
  intros. destruct H.
  - now apply simulation_beta.
  - now apply simulation_let.
  - now apply simulation_label.
Qed.

Lemma eta_fst_app s :
  App Fst s →* eta_fst s.
Proof.
  destruct s ; simpl ; try constructor. apply star_step, FullStep_step, Step_fst.
Qed.

Lemma eta_snd_app s :
  App Snd s →* eta_snd s.
Proof.
  destruct s ; simpl ; try constructor. apply star_step, FullStep_step, Step_snd.
Qed.

Lemma eta_fst_step s u :
  target_calculus.full_step s u -> eta_fst s →* eta_fst u.
Proof.
  intros. destruct H ; simpl.
  - destruct H ; simpl.
    + eapply star_trans.
       * apply app_star_r. apply star_step, FullStep_step, Step_beta.
       * apply eta_fst_app.
    + eapply star_trans.
       * apply app_star_r. apply star_step, FullStep_step, Step_let.
       * apply eta_fst_app.
    + eapply star_trans.
       * apply app_star_r. apply star_step, FullStep_step, Step_fst.
       * apply eta_fst_app.
    + eapply star_trans.
       * apply app_star_r. apply star_step, FullStep_step, Step_snd.
       * apply eta_fst_app.
    + apply app_star_r. apply star_step, FullStep_step, Step_join.
    + apply app_star_r. apply star_step, FullStep_step, Step_assoc.
    + eapply star_trans.
       * apply app_star_r. apply star_step, FullStep_step, Step_neutral.
       * apply eta_fst_app.
  - apply app_star_r. apply abs_star. econstructor ; eauto. constructor.
  - apply app_star_r. apply app_star_l. econstructor ; eauto. constructor.
  - apply app_star_r. apply app_star_r. econstructor ; eauto. constructor.
  - apply app_star_r. apply let_star_l. econstructor ; eauto. constructor.
  - apply app_star_r. apply let_star_r. econstructor ; eauto. constructor.
  - econstructor ; eauto. constructor.
  - constructor.
Qed.

Lemma eta_snd_step s u :
  target_calculus.full_step s u -> eta_snd s →* eta_snd u.
Proof.
  intros. destruct H ; simpl.
  - destruct H ; simpl.
    + eapply star_trans.
       * apply app_star_r. apply star_step, FullStep_step, Step_beta.
       * apply eta_snd_app.
    + eapply star_trans.
       * apply app_star_r. apply star_step, FullStep_step, Step_let.
       * apply eta_snd_app.
    + eapply star_trans.
       * apply app_star_r. apply star_step, FullStep_step, Step_fst.
       * apply eta_snd_app.
    + eapply star_trans.
       * apply app_star_r. apply star_step, FullStep_step, Step_snd.
       * apply eta_snd_app.
    + apply app_star_r. apply star_step, FullStep_step, Step_join.
    + apply app_star_r. apply star_step, FullStep_step, Step_assoc.
    + eapply star_trans.
       * apply app_star_r. apply star_step, FullStep_step, Step_neutral.
       * apply eta_snd_app.
  - apply app_star_r. apply abs_star. econstructor ; eauto. constructor.
  - apply app_star_r. apply app_star_l. econstructor ; eauto. constructor.
  - apply app_star_r. apply app_star_r. econstructor ; eauto. constructor.
  - apply app_star_r. apply let_star_l. econstructor ; eauto. constructor.
  - apply app_star_r. apply let_star_r. econstructor ; eauto. constructor.
  - constructor.
  - econstructor ; eauto. constructor.
Qed.

Lemma eta_fst_star s u :
  s →* u -> eta_fst s →* eta_fst u.
Proof.
  intros. induction H.
  - constructor.
  - apply eta_fst_step in H. eapply star_trans ; eauto.
Qed.

Lemma eta_snd_star s u :
  s →* u -> eta_snd s →* eta_snd u.
Proof.
  intros. induction H.
  - constructor.
  - apply eta_snd_step in H. eapply star_trans ; eauto.
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

Lemma simulation (e f : source_calculus.prefix) (He : is_term e) (Hf : is_term f) :
  e → f  -> exists u, ⦇e⦈  →* u /\ eta_eq u ⦇f⦈.
Proof.
  intros. induction H ; ainv ; simpl.
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

End Translation.