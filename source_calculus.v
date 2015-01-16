(* based on Pottier and Conchon, Information
    Flow Inference for Free *)

Require Import Autosubst.

Section SourceCalculus.

(* as in the original paper, for now we leave
     the set of labels entirely abstract *)

Parameter label : Set.

Inductive prefix : Type :=
| Hole
| Const (k : nat)
| Var (x : var)
| Abs (s : {bind prefix})
| App (s t : prefix)
| Let (s : prefix) (t : {bind prefix})
| Label (s : prefix) (l : label).

Instance Ids_prefix : Ids prefix. derive. Defined.
Instance Rename_prefix : Rename prefix. derive. Defined.
Instance Subst_prefix : Subst prefix. derive. Defined.
Instance SubstLemmas_prefix : SubstLemmas prefix. derive. Defined.

Inductive is_term : prefix -> Prop :=
| ConstTerm k : is_term (Const k)
| VarTerm x : is_term (Var x)
| AbsTerm s : is_term s -> is_term (Abs s)
| AppTerm s t : is_term s -> is_term t -> is_term (App s t)
| LetTerm s t : is_term s -> is_term t -> is_term (Let s t)
| LabelTerm s l : is_term s -> is_term (Label s l).

Inductive step : prefix -> prefix -> Prop :=
| Step_beta (s t : prefix) :
   step (App (Abs s) t) s.[t/]
| Step_let (s t : prefix) :
   step (Let s t) t.[s/]
| Step_lift (s t : prefix) (l : label) :
   step (App (Label s l) t) (Label (App s t) l).

Inductive full_step : prefix -> prefix -> Prop :=
| FullStep_step (s t : prefix) :
   step s t -> full_step s t
| FullStep_abs (s t : prefix) :
   full_step s t -> full_step (Abs s) (Abs t)
| FullStep_app_l (s s' t : prefix) :
   full_step s s' -> full_step (App s t) (App s' t)
| FullStep_app_r (s t t' : prefix) :
   full_step t t' -> full_step (App s t) (App s t')
| FullStep_let_l (s s' t : prefix) :
   full_step s s' -> full_step (Let s t) (Let s' t)
| FullStep_let_r (s t t' : prefix) :
   full_step t t' -> full_step (Let s t) (Let s t')
| FullStep_label (s t : prefix) (l : label) :
   full_step s t -> full_step (Label s l) (Label t l).
Notation "s → t" := (full_step s t) (at level 70).

Inductive star : prefix -> prefix -> Prop :=
| StarR p : star p p
| StarC x y z : x → y -> star y z -> star x z.
Notation "s →* t" := (star s t) (at level 70).

Inductive prefix_match : prefix -> prefix -> Prop :=
| HoleMatch p : prefix_match Hole p
| ConstMatch k1 k2 : k1 = k2 -> prefix_match (Const k1) (Const k2)
| VarMatch x1 x2 : x1 = x2 -> prefix_match (Var x1) (Var x2)
| AbsMatch s1 s2 : prefix_match s1 s2 -> prefix_match (Abs s1) (Abs s2)
| AppMatch s1 t1 s2 t2 : prefix_match s1 s2 -> prefix_match t1 t2 -> prefix_match (App s1 t1) (App s2 t2)
| LetMatch s1 t1 s2 t2 : prefix_match s1 s2 -> prefix_match t1 t2 -> prefix_match (Let s1 t1) (Let s2 t2)
| LabelMatch s1 l1 s2 l2 : l1 = l2 -> prefix_match s1 s2 -> prefix_match (Label s1 l1) (Label s2 l2).
Notation "s ⪯ t" := (prefix_match s t) (at level 70).

Lemma match_refl (e : prefix) :
  e ⪯ e.
Proof.
  induction e ; now constructor.
Qed.

Lemma match_trans (e1 e2 e3 : prefix) :
  e1 ⪯ e2 -> e2 ⪯ e3 -> e1 ⪯ e3.
Proof.
  intros. revert e3 H0. induction H ; intros.
  - constructor.
  - now subst.
  - now subst.
  - inversion H0 ; subst. constructor. apply IHprefix_match. exact H2.
  - inversion H1 ; subst. constructor ; auto.
  - inversion H1 ; subst. constructor ; auto.
  - inversion H1 ; subst. constructor ; auto.
Qed.

Lemma term_match (p1 p2 : prefix) :
  is_term p1 -> p1 ⪯ p2 -> p1 = p2.
Proof.
  intros. induction H0.
  - inversion H.
  - now subst.
  - now subst.
  - inversion H. now rewrite IHprefix_match.
  - inversion H. now rewrite IHprefix_match1, IHprefix_match2.
  - inversion H. now rewrite IHprefix_match1, IHprefix_match2.
  - inversion H. subst. now rewrite IHprefix_match.
Qed.

Lemma subst_match e e' sigma :
  e ⪯ e' -> e.[sigma] ⪯ e'.[sigma].
Proof.
  intros. revert sigma. induction H ; try now constructor.
  intros. subst. apply match_refl.
Qed.

Lemma match_up sigma sigma':
  (forall t, sigma t ⪯ sigma' t) -> (forall t, up sigma t ⪯ up sigma' t).
Proof.
  intros. induction t ; asimpl.
  - now constructor.
  - apply subst_match. apply H.
Qed.

Lemma subst_match2 s s' sigma sigma' :
  s ⪯ s' -> (forall t, sigma  t ⪯ sigma' t) -> s.[sigma] ⪯ s'.[sigma'].
Proof.
  intros. revert sigma sigma' H0. induction H ; intros.
  - constructor.
  - now constructor.
  - destruct x2 ; subst ; asimpl ; apply H0.
  - asimpl. constructor. apply IHprefix_match. intros. apply match_up. apply H0.
  - constructor ; auto.
  - constructor ; auto. apply IHprefix_match2. intros t. apply match_up. apply H1.
  - constructor ; auto.
Qed.

Lemma subst_match2' s s' t t' :
  s ⪯ s' -> t ⪯ t' -> s.[t/] ⪯ s'.[t'/].
Proof.
  intros. apply subst_match2.
  - exact H.
  - intros e. destruct e ; asimpl ; auto using prefix_match.
Qed.

Lemma match_step (p1 p2 p1': prefix) :
  p1 ⪯ p2 -> step p1 p1' -> exists p2', step p2 p2' /\ p1' ⪯ p2'.
Proof.
  intros. revert p2 H. induction H0 ; intros ; inversion H ; subst.
  - inversion H2 ; subst. exists s0.[t2/]. auto using step, subst_match2'.
  - exists t2.[s2/]. auto using step, subst_match2'.
  - inversion H2 ; subst. exists (Label (App s0 t2) l2). auto using step, prefix_match.
Qed.

Lemma match_fullstep (p1 p2 p1': prefix) :
  p1 ⪯ p2 -> p1 → p1' -> exists p2', p2 → p2' /\ p1' ⪯ p2'.
Proof.
  intros. revert p2 H. induction H0 ; intros.
  - destruct (match_step s p2 t) as [p2' []] ; auto. exists p2'. auto using full_step.
  - inversion H ; subst. destruct (IHfull_step s2) as [s2' []] ; auto.
    exists (Abs s2'). auto using full_step, prefix_match.
  - inversion H ; subst. destruct (IHfull_step s2) as [s2' []] ; auto.
    exists (App s2' t2). auto using full_step, prefix_match.
  - inversion H ; subst. destruct (IHfull_step t2) as [t2' []] ; auto.
    exists (App s2 t2'). auto using full_step, prefix_match.
  - inversion H ; subst. destruct (IHfull_step s2) as [s2' []] ; auto.
    exists (Let s2' t2). auto using full_step, prefix_match.
  - inversion H ; subst. destruct (IHfull_step t2) as [t2' []] ; auto.
    exists (Let s2 t2'). auto using full_step, prefix_match.
  - inversion H ; subst. destruct (IHfull_step s2) as [s2' []] ; auto.
    exists (Label s2' l2). auto using full_step, prefix_match.
Qed.

Lemma prefix_monotonicity (e e' f : prefix) :
  e ⪯ e' -> is_term f -> e →* f -> e' →* f.
Proof.
  intros. revert e' H. induction H1 as [e|e x f] ; intros.
  - rewrite (term_match e e') ; try constructor ; assumption.
  - destruct (match_fullstep e e' x) as [x' [H3 H4]] ; try assumption. assert (x' →* f) by auto.
    apply (StarC e' x' f) ; assumption.
Qed.

Definition label_filter (p : label -> bool) :=
  fix f (e : prefix) := match e with
  | Label e l => if p l then Label (f e) l else Hole
  | Hole => Hole
  | Const k => Const k
  | Var x => Var x
  | Abs e => Abs (f e)
  | App e1 e2 => App (f e1) (f e2)
  | Let e1 e2 => Let (f e1) (f e2)
  end. 
Notation "⌊ e ⌋ p" := (label_filter p e) (at level 70).

Lemma ren_filter (sigma : var -> prefix) xi p : sigma >>> (label_filter p >>> subst (xi >>> ids)) = (sigma >>> subst (xi >>> ids)) >>> label_filter p.
Proof.
  f_ext. intros. simpl. generalize (sigma x). intros s. revert xi. induction s; intros; asimpl; try f_equal; eauto.
  destruct (p l); asimpl; try f_equal; eauto.
Qed.

Hint Rewrite @ren_filter : autosubst.

Lemma filter_subst p e sigma:
  (⌊ e ⌋p).[sigma >>> label_filter p] = ⌊ e.[sigma] ⌋p.
Proof.
  revert sigma. induction e ; intros.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - asimpl. rewrite <- IHe. autosubst.
  - simpl. now rewrite IHe1, IHe2.
  - asimpl. f_equal.
    + apply IHe.
    + rewrite <- IHe0. autosubst.
  - simpl. destruct (p l).
    + simpl. now rewrite IHe.
    + simpl. reflexivity.
Qed.

Lemma filter_beta p e1 e2 :
  ⌊ App (Abs e1) e2 ⌋p → ⌊ e1.[e2/] ⌋p.
Proof.
  rewrite <- filter_subst. asimpl. auto using step, full_step.
Qed.

Lemma filter_let p e1 e2 :
  ⌊ Let e1 e2 ⌋p → ⌊ e2.[e1/] ⌋p.
Proof.
  rewrite <- filter_subst. asimpl. auto using step, full_step.
Qed.

Lemma filter_lift p e1 e2 l :
  p l = true -> ⌊ App (Label e1 l) e2 ⌋p → ⌊ Label (App e1 e2) l ⌋p.
Proof.
  intros. simpl. rewrite H. auto using step, full_step.
Qed.

Lemma filter_step {s s'} :
  step s s' -> forall p, (⌊ s ⌋p → ⌊ s' ⌋p) \/ ⌊ s' ⌋p ⪯ ⌊ s ⌋p.
Proof.
  intros. induction H.
  - left. apply filter_beta.
  - left. apply filter_let.
  - case_eq (p l) ; intros.
    + left. now apply filter_lift.
    + simpl. rewrite H. right. constructor.
Qed.

Lemma filter_fullstep {s s'} :
  s → s' -> forall p, (⌊ s ⌋p → ⌊ s' ⌋p) \/ ⌊ s' ⌋p ⪯ ⌊ s ⌋p.
Proof.
  intros. induction H ; simpl.
  - now apply filter_step.
  - destruct IHfull_step ; auto using full_step, prefix_match.
  - destruct IHfull_step ; auto using full_step, prefix_match, match_refl.
  - destruct IHfull_step ; auto using full_step, prefix_match, match_refl.
  - destruct IHfull_step ; auto using full_step, prefix_match, match_refl.
  - destruct IHfull_step ; auto using full_step, prefix_match, match_refl.
  - case_eq (p l) ; intros.
    + destruct IHfull_step ; auto using full_step, prefix_match.
    + auto using prefix_match.
Qed.

Theorem stability e f p :
  is_term f -> e →* f -> ⌊ f ⌋p = f -> ⌊ e ⌋p →* f.
Proof.
  intros. induction H0.
  - rewrite H1. constructor.
  - destruct (filter_fullstep H0 p).
    + econstructor ; eauto.
    + eapply prefix_monotonicity ; eauto.
Qed.

End SourceCalculus.
