(* In this file we define the source calculus - a simple programming
   language capable of expressing information flow that will be
   compiled down to a typed target calculus such that the target
   calculus' type system can enforce the information flow constraints
   without any security typing built-in. The idea is that the target
   calculus may be some already existing language with a
   sufficiently strong type system; by compiling our
   information flow sensitive language into it and verifying the
   correctness of our translation, we can effectively type the
   source calculus without reproving correctness of the extended
   type system. *)

(* Pottier & Conchon have the luxury of eliding details of
   substitution, as is standard [cite]. Unfortunately, our mechanized
   development in Coq cannot afford to do such a thing; thus, our
   implementations of the calculi use a traditional de Bruijn-style
   representation for bound variables [cite], where variables are
   represented as natural numbers indicating the structural
   distance to their binder. Implementing substitution using this
   scheme in Coq turns out to be rather burdensome [cite]; to help,
   we rely on Autosubst [cite], a library developed by Steven
   Schäfer and Tobias Tebbi designed to ease the process by
   generating the substitution operation and useful associated
   lemmas; it also provides various automation tactics to
   make writing proofs involving substitution easier. *)

Require Import Autosubst.

Require Import labels.

Section SourceCalculus.

(* Our source calculus is a standard lambda calculus with labels.
   What follows is a definition of *prefixes*, not terms -
   a prefix is a term that optionally may have a "hole", a "missing
   subexpression"; to put it another way, terms are the subset of
   prefixes containing no holes. *)

(* The original paper defines prefixes as an extension of the set of
   terms. As Coq doesn't provide any means of extending inductive
   type definitions, we instead use one general prefix type and rely
   on an is_term predicate to restrict the scope of lemmas when
   necessary. This avoids definitional duplication (even if the
   is_term definition strongly resembles the prefix definition) and
   ensures lemmas are as general as possible. *)

(* Note the use of the {bind prefix} type. This is how we inform
   Autosubst that the given term binds a variable. *)

Inductive prefix : Type :=
| Hole
| Const (k : nat)
| Var (x : var)
| Abs (s : {bind prefix})
| App (s t : prefix)
| Let (s : prefix) (t : {bind prefix})
| Label (s : prefix) (l : label).

(* Here we use Autosubst to automatically generate the substitution
   operation and lemmas for our type *)

Instance Ids_prefix : Ids prefix. derive. Defined.
Instance Rename_prefix : Rename prefix. derive. Defined.
Instance Subst_prefix : Subst prefix. derive. Defined.
Instance SubstLemmas_prefix : SubstLemmas prefix. derive. Defined.

(* Here we define a predicate that indicates if a prefix is a term,
   i.e. has no holes *)
Inductive is_term : prefix -> Prop :=
| ConstTerm k : is_term (Const k)
| VarTerm x : is_term (Var x)
| AbsTerm s : is_term s -> is_term (Abs s)
| AppTerm s t : is_term s -> is_term t -> is_term (App s t)
| LetTerm s t : is_term s -> is_term t -> is_term (Let s t)
| LabelTerm s l : is_term s -> is_term (Label s l).

(* One of the biggest differences between our implementation of
   Pottier & Conchon's method and the original paper is our
   treatment of evaluation contexts. Whereas Potter & Conchon
   introduce a context rule that allows the evaluation relation
   to be, in a sense, parametric over different evaluation strategies
   (notably call-by-name, call-by-value, and full reduction), we
   instead define a base evaluation relation and then embed it
   inside the proper evaluation strategies, eschewing the
   notion of evaluation contexts altogether. *)

(* The only rule in our base evaluation relation that's non-standard
   is the "lift" rule, which allows labels to "bubble up". This way
   we can easily the labels of the data a computation relied on.
   This is precisely how we implemented information flow
   sensitivity for security typing - if we have the traditional set
   of L and H labels, we can determine if a computation relied on
   H-labelled data. *)

Inductive step : prefix -> prefix -> Prop :=
| Step_beta (s t : prefix) :
   step (App (Abs s) t) s.[t/]
| Step_let (s t : prefix) :
   step (Let s t) t.[s/]
| Step_lift (s t : prefix) (l : label) :
   step (App (Label s l) t) (Label (App s t) l).

(* Full reduction is standard *)

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

(* We use a →-notation for full reduction, as most of the
   lemmas and theorems we prove in this section are for full
   reduction. This means that our lemmas appear in Coq to match
   the notation used in the original Pottier & Conchon paper
   (clarified in private correspondance with the author). *)

Notation "s → t" := (full_step s t) (at level 70).

(* We define a standard transitive reflexive closure over
   full reduction *)

Inductive star : prefix -> prefix -> Prop :=
| StarR p : star p p
| StarC x y z : x → y -> star y z -> star x z.
Notation "s →* t" := (star s t) (at level 70).

(* A prefix "matches" another prefix if it is the
   same except for some subexpressions possibly replaced by
   holes. *)

Inductive prefix_match : prefix -> prefix -> Prop :=
| HoleMatch p : prefix_match Hole p
| ConstMatch k1 k2 : k1 = k2 -> prefix_match (Const k1) (Const k2)
| VarMatch x1 x2 : x1 = x2 -> prefix_match (Var x1) (Var x2)
| AbsMatch s1 s2 :
    prefix_match s1 s2 -> prefix_match (Abs s1) (Abs s2)
| AppMatch s1 t1 s2 t2 :
    prefix_match s1 s2 -> prefix_match t1 t2 ->
    prefix_match (App s1 t1) (App s2 t2)
| LetMatch s1 t1 s2 t2 :
    prefix_match s1 s2 -> prefix_match t1 t2 ->
    prefix_match (Let s1 t1) (Let s2 t2)
| LabelMatch s1 l1 s2 l2 :
    l1 = l2 -> prefix_match s1 s2 ->
    prefix_match (Label s1 l1) (Label s2 l2).
Notation "s ⪯ t" := (prefix_match s t) (at level 70).

(* it's a useful and trivial result that matching is a relfexive
   operation - all prefixes match themselves *)
Lemma match_refl (e : prefix) :
  e ⪯ e.
Proof.
  induction e ; now constructor.
Qed.

(* Following the original paper, the first lemma we're interested
   in showing about our source calculus is "prefix monotonicty",
   which states that reduction sequences are preserved even
   if we replace holes with valid subexpressions. Prefix
   monotonicity will be necessary to show the key theorem about our
   source calculus, stability (described shortly).

   The paper provides no proof for prefix monotonicity. We first
   rely on a simple lemma that states that a term (i.e. a prefix
   with no holes) matches only itself, a fact that falls quite
   trivially out of the induction. *)

Lemma term_match (p1 p2 : prefix) :
  is_term p1 -> p1 ⪯ p2 -> p1 = p2.
Proof.
  induction 2 ; ainv ; now autorew.
Qed.

(* Next, we need to prove a series of rather technical lemmas
   related to substitution. The first states that
   any substitution will preserve matchings, which makes intuitive
   sense - any holes will remain holes on the left (matching
   because holes match anything), and any substitution on the left
   will happen in precisely the same way on the right (matching due
   to reflexivity of matchings). *)

Lemma subst_match e e' sigma :
  e ⪯ e' -> e.[sigma] ⪯ e'.[sigma].
Proof.
  intro H. revert sigma. induction H ; try now constructor.
  intros. subst. apply match_refl.
Qed.

(* We might think of two substitutions as matching if the terms
   they substitute in always match. *)

Definition matching_substitutions (sigma sigma' : var -> prefix) :=
  forall t, sigma t ⪯ sigma' t.

(* The up-operation is generated by Autosubst and applied to
   substitutions when operating under a binder [cite].
   We need to show that a pair of matching substitutions will
   continue to match once up has been applied to them. *)

Lemma match_up sigma sigma':
  matching_substitutions sigma sigma' ->
  matching_substitutions (up sigma) (up sigma').
Proof.
  intros H t. destruct t ; asimpl.
  - now constructor.
  - apply subst_match, H.
Qed.

(* subst_match tells us that if two prefixes match, we can
   apply a single substitution to them and the result will match;
   subst_match2 strengthens this: we can, in fact, apply two
   *different* substitutions, as long as the first matches the
   second, and preserve the matching *)

Lemma subst_match2 s s' sigma sigma' :
  s ⪯ s' ->
  matching_substitutions sigma sigma' ->
  s.[sigma] ⪯ s'.[sigma'].
Proof.
  intros H. revert sigma sigma'. induction H ; intros ; simpl.
  - constructor.
  - now constructor.
  - subst. apply H0.
  - constructor. apply IHprefix_match. now apply match_up.
  - constructor ; auto.
  - constructor ; auto. apply IHprefix_match2. now apply match_up.
  - constructor ; auto.
Qed.

(* The following is a simple corollary of subst_match2,
   restricted to single term substitutions *)

Corollary subst_match2' s s' t t' :
  s ⪯ s' -> t ⪯ t' -> s.[t/] ⪯ s'.[t'/].
Proof.
  intros. apply subst_match2.
  - assumption.
  - intros e. destruct e ; asimpl ; auto using prefix_match.
Qed.

(* The final major result we need before proving prefix monotonicity,
   and what these substitution lemmas have been leading to, is
   this match_step result, which shows that we can "lift" a
   reduction step onto a matching prefix and our lifting will
   preserve the matching. Effectively this is prefix monotonicity
   for a single step, rather than a reduction sequence.

   Because the full reduction relation is actually divided between
   the step and full_step predicates, we need two lemmas to prove
   this result. *)

Lemma match_step (p1 p2 p1': prefix) :
  p1 ⪯ p2 -> step p1 p1' -> exists p2', step p2 p2' /\ p1' ⪯ p2'.
Proof.
  intros H H0. revert p2 H. induction H0 ; intros ; ainv.
  - exists s0.[t2/] ; auto using step, subst_match2'.
  - exists t2.[s2/] ; auto using step, subst_match2'.
  - exists (Label (App s0 t2) l2) ; auto using step, prefix_match.
Qed.

Lemma match_fullstep (p1 p2 p1': prefix) :
  p1 ⪯ p2 -> p1 → p1' -> exists p2', p2 → p2' /\ p1' ⪯ p2'.
Proof.
  intros H H0. revert p2 H. induction H0 ; intros ; ainv.
  - destruct (match_step s p2 t) as [p2' []] ; auto. exists p2' ; auto using full_step.
  - destruct (IHfull_step s2) as [s2' []] ; auto.
    exists (Abs s2') ; auto using full_step, prefix_match.
  - destruct (IHfull_step s2) as [s2' []] ; auto.
    exists (App s2' t2) ; auto using full_step, prefix_match.
  - destruct (IHfull_step t2) as [t2' []] ; auto.
    exists (App s2 t2') ; auto using full_step, prefix_match.
  - destruct (IHfull_step s2) as [s2' []] ; auto.
    exists (Let s2' t2) ; auto using full_step, prefix_match.
  - destruct (IHfull_step t2) as [t2' []] ; auto.
    exists (Let s2 t2') ; auto using full_step, prefix_match.
  - destruct (IHfull_step s2) as [s2' []] ; auto.
    exists (Label s2' l2) ; auto using full_step, prefix_match.
Qed.

Lemma prefix_monotonicity (e e' f : prefix) :
  e ⪯ e' -> is_term f -> e →* f -> e' →* f.
Proof.
  intros H H0 H1. revert e' H. induction H1 as [e|e x f] ; intros.
  - rewrite (term_match e e') ; eauto using star.
  - destruct (match_fullstep e e' x) as [x' [H3 H4]] ; auto.
    eauto using star.
Qed.

(* Following the original paper, the primary result we want to prove
   for the source calculus is stability, which roughly states that
   the labels contained in the result of a reduction sequence are the
   only labels the reduction sequence depends on - that is,
   they can be stripped out of the initial term of the reduction
   sequence and the sequence will still work.

   Stability is a key element of our proof of non-interference. *)

(* First, we need a way to talk about the labels contained in a
   term. Rather than collect these directly, we introduce
   notation that strips a set of labels out of a term.
   If a term remains the same after some set of labels is stripped
   out, then obviously it doesn't contain any of the labels in the
   set.

   The original paper uses standard informal mathematical sets.
   Here, we concretely represent this as a decidable boolean
   predicate for set membership. *)

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

(* Again, we won't be able to prove our desired theorem directly.
   First, we need to teach autosubst [etc] *)

Lemma ren_filter xi p :
  label_filter p >>> subst (xi >>> ids)
= subst (xi >>> ids) >>> label_filter p.
Proof.
  f_ext. intro s. revert xi.
  induction s; intros; asimpl; try f_equal; eauto.
  destruct (p l); asimpl; try f_equal; eauto.
Qed.

(* This teaches Autosubst to use this rewrite rule with its
   autosubst tactic, to help make proofs using it go smoothly *)
Hint Rewrite @ren_filter : autosubst.

(* This lemma's rather technical result is probably easier to read
   formally rather than described informally. The key thing to note
   is that sigma >>> label_filter p is a substitution that is, in a
   sense, the filtering of sigma: the sigma substitution is
   performed, but each term that is substituted in is filtered
   first

   This lemma is necessary for a series of lemmas that follow which
   roughly corresponding to Lemma 3.2 in the paper. *)
Lemma filter_subst p e sigma:
  (⌊ e ⌋p).[sigma >>> label_filter p] = ⌊ e.[sigma] ⌋p.
Proof.
  revert sigma. induction e ; intros ; asimpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite <- IHe. autosubst.
  - now rewrite IHe1, IHe2.
  - f_equal.
    + apply IHe.
    + rewrite <- IHe0. autosubst.
  - destruct (p l) ; simpl.
    + now rewrite IHe.
    + reflexivity.
Qed.

(* As mentioned, each of these lemmas corresponds to a subcase of
   Lemma 3.2 in the paper. Much as match_step was for
   prefix_monotonicity, they serve as a kind of weakening of
   stability for a single step. *)

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
  simpl. intros H ; rewrite H. auto using step, full_step.
Qed.

(* Note the difference between this and Lemma 3.2 [etc]

   As with match_step, we need lemmas both for the basic step
   relation and the expanded fullstep relation. *)

Lemma filter_step s s' :
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

(* Finally, we have the proof of stability. *)
Theorem stability e f p :
  is_term f -> e →* f -> ⌊ f ⌋p = f -> ⌊ e ⌋p →* f.
Proof.
  intros. induction H0.
  - rewrite H1. constructor.
  - destruct (filter_fullstep H0 p).
    + econstructor ; eauto.
    + eapply prefix_monotonicity ; eauto.
Qed.

(* With stability proven, we now define predicates and lemmas over
   the source calculus used for other parts of the development. *)

(* The paper defines the typing relation solely over closed terms;
   thus, we need a way to talk about closedness. The following
   approach is taken from [Semantics course notes]; a term is
   n_closed n if all free variables in it are less than n (recall
   that variables are represented by natural numbers). An
   n_closed 0 term is thus fully closed, as all free variables
   in this term are less than 0 (i.e. do not exist). This approach
   is often necessary, rather than defining is_closed directly, to
   exploit induction over terms (as the subterm of a closed term may
   not be fully closed, i.e. Abs (Var 0) is closed, but Var 0 is
   only n_closed 1). *)

Inductive n_closed (n : nat) : prefix -> Prop :=
| ConstClosed k : n_closed n (Const k)
| VarClosed x : x < n -> n_closed n (Var x)
| AbsClosed s : n_closed (S n) s -> n_closed n (Abs s)
| LetClosed s t : n_closed n s -> n_closed (S n) t -> n_closed n (Let s t)
| AppClosed s t : n_closed n s -> n_closed n t -> n_closed n (App s t)
| LabelClosed s l : n_closed n s -> n_closed n (Label s l).

Definition is_closed := n_closed 0.

(* The definition of values in our calculus is standard and taken
   from section 6.1; it's necessary to specify non-interference
   and progress *)

Inductive is_value : prefix -> Prop :=
| Value_const k : is_value (Const k)
| Value_abs e : is_value (Abs e)
| Value_label l v : is_value v -> is_value (Label v l).

(* Our definition of call-by-need is again standard and taken
   from section 6.1 of the Pottier & Conchon paper. We'll need to
   define CBN to talk about progress. *)

Inductive cbn : prefix -> prefix -> Prop :=
| CBN_step s t : step s t -> cbn s t
| CBN_app s s' t : cbn s s' -> cbn (App s t) (App s' t)
| CBN_label s s' l : cbn s s' -> cbn (Label s l) (Label s' l).

(* The proof of non-interference will require a result called
   term_star, which shows that reduction cannot introduce holes -
   if a prefix is a term, it remains a term under reduction.
   We prove this for single steps, and then for reduction
   sequences; several preliminary lemmas concerning substitutions
   are required as well. *)

(* We say a substitution is subst_term if it does not introduce any
   non-term prefixes. *)
Definition subst_term sigma := forall (x : var), is_term (sigma x).

(* All renamings have a similar property *)
Lemma ren_term s r :
  is_term s -> is_term s.[ren r].
Proof.
  revert r.
  induction s ; intros ; asimpl ; ainv ; constructor ; auto.
Qed.

(* If a substitution is subst_term, applying the up operator to it
   preserves this property *)
Lemma up_subst_term sigma :
  subst_term sigma -> subst_term (up sigma).
Proof.
  intros H x. destruct x ; asimpl.
  - constructor.
  - apply ren_term, H.
Qed.

(* Applying a subst_term substitution to a term results in a term *)
Lemma term_repl s sigma :
  is_term s -> subst_term sigma -> is_term s.[sigma].
Proof.
  revert sigma. induction s ; intros ; simpl ; ainv ;
    auto using is_term, up_subst_term.
Qed.

(* a single variable substitution is subst_term *)
Lemma scons_subst_term t :
  is_term t -> subst_term (t .: ids).
Proof.
  intros. intro x. destruct x ; simpl.
  - assumption.
  - constructor.
Qed.

Lemma term_step e f :
  is_term e -> step e f -> is_term f.
Proof.
  induction 2 ; ainv.
  - apply term_repl ; auto using scons_subst_term.
  - apply term_repl ; auto using scons_subst_term.
  - repeat constructor ; auto.
Qed.

Lemma term_full_step e f :
  is_term e -> full_step e f -> is_term f.
Proof.
  induction 2 ; ainv.
  - eapply term_step ; eauto.
  - constructor. now apply IHfull_step.
  - constructor ; auto.
  - constructor ; auto.
  - constructor ; auto.
  - constructor ; auto.
  - constructor ; auto.
Qed.

Lemma term_star e f :
  is_term e -> star e f -> is_term f.
Proof.
  induction 2 ; eauto using term_full_step.
Qed.

End SourceCalculus.

(* Export this notation *)
Notation "⌊ e ⌋ p" := (label_filter p e) (at level 70).
