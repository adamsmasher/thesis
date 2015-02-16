Require Import Autosubst.
Require Import poset.
Require Import semilattice.

Section TargetCalculus.

Parameter label : Set.
Parameter label_eq : forall (l1 l2 : label), {l1 = l2} + {~l1 = l2}.
Parameter precedes : label -> label -> Prop.
Parameter bottom : label.
Parameter join : label -> label -> label.
Parameter poset : Poset label precedes.
Parameter semilattice : UpperSemiLattice poset join bottom.

Notation "l ⋎ m" := (join l m) (at level 70).

Inductive term : Type :=
| Const (k : nat)
| Var (x : var)
| Abs (s : {bind term})
| App (s t : term)
| Let (s : term) (t : {bind term})
| Pair (s t : term)
| Fst
| Snd
| Label (l : label)
| Join.

Inductive isValue : term -> Prop :=
| const_value k : isValue (Const k)
| abs_value s : isValue (Abs s)
| fst_value : isValue Fst
| snd_value : isValue Snd
| label_value l : isValue (Label l)
| join_value : isValue Join.

Notation "l @ m" := (App (App Join l) m) (at level 70).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Defined.

Inductive step : term -> term -> Prop :=
| Step_beta (s t : term) :
   step (App (Abs s) t) s.[t/]
| Step_let (s t : term) :
   step (Let s t) t.[s/]
| Step_fst s t :
   step (App Fst (Pair s t)) s
| Step_snd s t :
   step (App Snd (Pair s t)) t
| Step_join l m :
   step ((Label l) @ (Label m)) (Label (l ⋎ m))
| Step_assoc s t u :
   step ((s @ t) @ u) (s @ (t @ u))
| Step_neutral s :
   step ((Label bottom) @ s) s.

Inductive full_step : term -> term -> Prop :=
| FullStep_step s t :
   step s t -> full_step s t
| FullStep_abs s t :
   full_step s t -> full_step (Abs s) (Abs t)
| FullStep_app_l s s' t :
   full_step s s' -> full_step (App s t) (App s' t)
| FullStep_app_r s t t' :
   full_step t t' -> full_step (App s t) (App s t')
| FullStep_let_l s s' t :
   full_step s s' -> full_step (Let s t) (Let s' t)
| FullStep_let_r s t t' :
   full_step t t' -> full_step (Let s t) (Let s t')
| FullStep_pair_l s s' t :
   full_step s s' -> full_step (Pair s t) (Pair s' t)
| FullStep_pair_r s t t':
   full_step t t' -> full_step (Pair s t) (Pair s t').

Notation "s → t" := (full_step s t) (at level 70).

Inductive star : term -> term -> Prop :=
| StarR p : star p p
| StarC x y z : x → y -> star y z -> star x z.
Notation "s →* t" := (star s t) (at level 70).

Lemma star_step s t :
  s → t -> s →* t.
Proof.
  intros. eapply StarC.
  + apply H.
  + apply StarR.
Qed.

Lemma star_trans s t u :
  s →* t -> t →* u -> s →* u.
Proof.
  intros. revert u H0. induction H ; intros ; simpl.
  - assumption.
  - eapply StarC. eassumption. apply IHstar. assumption.
Qed.

Lemma pair_star_l s s' t:
  s →* s' -> Pair s t →* Pair s' t.
Proof.
  intros ; induction H ; eauto using step, full_step, star.
Qed.

Lemma pair_star_r s t t' :
  t →* t' -> Pair s t →* Pair s t'.
Proof.
  intros ; induction H ; eauto using step, full_step, star.
Qed.

Lemma pair_star s s' t t' :
  s →* s' -> t →* t' ->  Pair s t →* Pair s' t'.
Proof.
  intros. eapply star_trans.
  - apply pair_star_l, H.
  - apply pair_star_r, H0.
Qed.

Lemma app_star_l s s' t :
  s →* s' -> App s t →* App s' t.
Proof.
  intros. induction H ; eauto using step, full_step, star.
Qed.

Lemma app_star_r s t t' :
  t →* t' -> App s t →* App s t'.
Proof.
  intros. induction H ; eauto using step, full_step, star.
Qed.

Lemma app_star s s' t t' :
  s →* s' ->  t →* t' -> App s t →* App s' t'.
Proof.
  intros. eapply star_trans.
  apply app_star_l, H.
  apply app_star_r, H0.
Qed.

Lemma let_star_l s s' t :
  s →* s' -> Let s t →* Let s' t.
Proof.
  intros. induction H ; eauto using step, full_step, star.
Qed.

Lemma let_star_r s t t' :
  t →* t' -> Let s t →* Let s t'.
Proof.
  intros. induction H ; eauto using step, full_step, star.
Qed.

Lemma let_star s s' t t' :
  s →* s' ->  t →* t' -> Let s t →* Let s' t'.
Proof.
  intros. eapply star_trans.
  apply let_star_l, H.
  apply let_star_r, H0.
Qed.

Lemma abs_star s s' :
  s →* s' -> Abs s →* Abs s'.
Proof.
  intros. induction H ; eauto using step, full_step, star.
Qed.

End TargetCalculus.