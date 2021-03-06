Require Import Autosubst.
Require Import labels.

Section TargetCalculus.

(* The target calculus is basic functional programming language with
   terms representing labels, a join function operating over them,
   and pairs. *)

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

(* We introduce some notation, matching the paper, to make it
   easier to write out term level joins *)

Notation "l @ m" := (App (App Join l) m) (at level 70).

(* As with the source calculus, we use Autosubst to get
   the substitution operation and lemmas. *)

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Defined.

(* The target calculus step relation is adapted from the paper in
   much the same way as the source calculus' step relation was.

   Note that our step relation is the extended one, notated in the
   paper as →@; that is, it includes the assoc and neutral to help
   reason about the label join operation. *)

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

(* As per usual, we define a reflexive, transitive closure for the
   full step relation *)

Inductive star : term -> term -> Prop :=
| StarR p : star p p
| StarC x y z : x → y -> star y z -> star x z.
Notation "s →* t" := (star s t) (at level 70).

Lemma star_trans s t u :
  s →* t -> t →* u -> s →* u.
Proof.
  intros. induction H ; intros ; simpl.
  - assumption.
  - eapply StarC.
    + eassumption.
    + apply IHstar. assumption.
Qed.

(* The paper doesn't prove any lemmas about the target calculus;
   the following lemmas are simply for convenience when working with
   it. *)

(* steps can be lifted into one step reduction sequences *)
Lemma star_step s t :
  s → t -> s →* t.
Proof.
  intro H. eapply StarC.
  + apply H.
  + apply StarR.
Qed.

Lemma abs_star s s' :
  s →* s' -> Abs s →* Abs s'.
Proof.
  intros. induction H ; eauto using step, full_step, star.
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

(* Because the type system will operate over closed terms of
   the target calculus, we need a way to talk about closedness.
   This approach is identical to that used in the source calculus. *)

Inductive n_closed (n : nat) : term -> Prop :=
| ConstClosed k : n_closed n (Const k)
| VarClosed x : x < n -> n_closed n (Var x)
| AbsClosed s : n_closed (S n) s -> n_closed n (Abs s)
| LetClosed s t : n_closed n s -> n_closed (S n) t -> n_closed n (Let s t)
| AppClosed s t : n_closed n s -> n_closed n t -> n_closed n (App s t)
| PairClosed s t : n_closed n s -> n_closed n t -> n_closed n (Pair s t)
| FstClosed : n_closed n Fst
| SndClosed : n_closed n Snd
| JoinClosed : n_closed n Join
| LabelClosed l : n_closed n (Label l).

Definition is_closed := n_closed 0.

(* A key axiom necessary to type the target calculus is
   compositionality - a closed subexpression of a well-typed term
   is also well-typed. The following predicate is thus necessary
   to formalize the notion of a subexpression. *)

Inductive is_subexpr : term -> term -> Prop :=
| Sub_abs s : is_subexpr s (Abs s)
| Sub_app_l s t : is_subexpr s (App s t)
| Sub_app_r s t : is_subexpr t (App s t)
| Sub_let_l s t : is_subexpr s (Let s t)
| Sub_let_r s t : is_subexpr t (Let s t)
| Sub_pair_l s t : is_subexpr s (Pair s t)
| Sub_pair_r s t : is_subexpr t (Pair s t)
| Sub_trans s t u :
    is_subexpr s t -> is_subexpr t u -> is_subexpr s u.

(* Another crucial type system axiom is progress - a term either
   is CBN-reducible or is a value. We formalize these notions below.
   Note that the CBN step relation is similar to the full step
   relation above in how extends the base step relation. *)

Inductive cbn : term -> term -> Prop :=
| CBN_step s t :
   step s t -> cbn s t
| CBN_app s s' t :
   cbn s s' -> cbn (App s t) (App s' t)
| CBN_fst s s' :
   cbn s s' -> cbn (App Fst s) (App Fst s')
| CBN_snd s s' :
   cbn s s' -> cbn (App Snd s) (App Snd s')
| CBN_join_l s s' :
   cbn s s' -> cbn (App Join s) (App Join s')
| CBN_join_r s t t' :
   cbn t t' -> cbn (App (App Join s) t) (App (App Join s) t').

Inductive is_value : term -> Prop :=
| Value_const k : is_value (Const k)
| Value_abs e : is_value (Abs e)
| Value_pair s t : is_value (Pair s t)
| Value_fst : is_value Fst
| Value_snd : is_value Snd
| Value_label l : is_value (Label l)
| Value_join : is_value Join
| Value_join_label l : is_value (App Join (Label l)).

End TargetCalculus.

(* This is duplicated outside of the section so that it's visible
   in other modules. *)
Notation "l @ m" := (App (App Join l) m) (at level 70).
