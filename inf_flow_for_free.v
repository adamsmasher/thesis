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

Fixpoint is_term (p : prefix) : Prop := match p with
| Hole => False
| Const _ => True
| Var _ => True
| Abs s => is_term s
| App s t => is_term s /\ is_term t
| Let s t => is_term s /\ is_term t
| Label s _ => is_term s
end.

(* notion of contexts taken from Proving ML Type Soundness Within Coq by Catherine Dubois *)
(* for now our contexts are abstract *)
Definition eval_ctx := prefix -> prefix.
Parameter is_context : eval_ctx -> Prop.

Inductive step : prefix -> prefix -> Prop :=
| Step_beta (s t : prefix) :
   step (App (Abs s) t) s.[t/]
| Step_let (s t : prefix) :
   step (Let s t) t.[s/]
| Step_lift (s t : prefix) (l : label) :
   step (App (Label s l) t) (Label (App s t) l)
| Step_context (s1 s2 : prefix) (E : eval_ctx) :
   is_context E -> step s1 s2 ->
   step (E s1) (E s2).
Notation "s → t" := (step s t) (at level 70).

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

Lemma term_match (p1 p2 : prefix) :
  is_term p1 -> p1 ⪯ p2 -> p1 = p2.
Proof.
  intros. induction H0.
  - simpl in H. contradiction.
  - now subst.
  - now subst.
  - simpl in H. now rewrite IHprefix_match.
  - simpl in H. destruct H. now rewrite IHprefix_match1, IHprefix_match2.
  - simpl in H. destruct H. now rewrite IHprefix_match1, IHprefix_match2.
  - simpl in H. now rewrite IHprefix_match, H0.
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
  intros. induction t.
  - asimpl. now constructor.
  - asimpl. apply subst_match. apply H.
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
  - intros e. induction e.
    + auto.
    + simpl. now constructor.
Qed.

Lemma match_step (p1 p2 p1': prefix) :
  p1 ⪯ p2 -> p1 → p1' -> exists p2', p2 → p2' /\ p1' ⪯ p2'.
Proof.
  intros. induction H0.
  - inversion H ; subst. inversion H2 ; subst. exists s0.[t2/]. split.
    + constructor.
    + apply subst_match2' ; assumption.
  - inversion H ; subst. exists t2.[s2/]. split.
    + constructor.
    + apply subst_match2' ; assumption.
  - inversion H ; subst. inversion H2 ; subst. exists (Label (App s0 t2) l2). split ; constructor ; auto.
    constructor ; assumption.
  -
Admitted.

Lemma prefix_monotonicity (e e' f : prefix) :
  e ⪯ e' -> is_term f -> e →* f -> e' →* f.
Proof.
  intros. revert e' H. induction H1 as [e|e x f].
  - intros. rewrite (term_match e e') ; try constructor ; assumption.
  - intros. destruct (match_step e e' x) as [x' [H3 H4]] ; try assumption. assert (x' →* f).
    { apply IHstar ; assumption. }
    apply (StarC e' x' f) ; assumption.
Qed.

End SourceCalculus.

(* lattice stuff influenced by A reflection-based
proof tactic for lattices in Coq by Daniel James
and Ralf Hinze *)

(* also: A Gentle Introducton to Type Classes and
    Relations in Coq by Pierre Casteran *)
    
Class UpperSemiLattice (A : Set) := {
  join : A -> A -> A;

  join_commutative : forall a b, join a b = join b a;
  join_associatve : forall a b c, join (join a b) c = join a (join b c);
  join_idempotent : forall a, join a a =a
}.
