Require Import source_calculus.
Require Import target_calculus.

Require Import Autosubst.

Section Translation.

Parameter label_eq : source_calculus.label = target_calculus.label.

Definition translate_label (l : source_calculus.label) : target_calculus.label.
  rewrite <- label_eq. exact l.
Defined.

Definition reify_pair (p : term * term) : term := Pair (fst p) (snd p).

Notation "l @ m" := (App (App Join l) m) (at level 70).

Definition translation (e : source_calculus.prefix) (H : is_term e) : prod target_calculus.term target_calculus.term.
  induction e.
  - exfalso. inversion H.
  - split.
    + exact (Const k).
    + exact (Label bottom).
  - split.
    + exact (App Fst (Var x)).
    + exact (App Snd (Var x)).
  - split.
    + assert (H' : is_term s) by now inversion H. exact (Abs (reify_pair (IHe H'))).
    + exact (Label bottom).
  - assert (H1 : is_term e1) by now inversion H. assert (H2 : is_term e2) by now inversion H.
    destruct (IHe1 H1) as [e1_1 e1_2]. pose (e2' := (reify_pair (IHe2 H2))). split.
    + exact (App Fst (App e1_1 e2')).
    + exact (e1_2 @ (App Snd (App e1_1 e2'))).
  - assert (He : is_term e) by now inversion H. assert (Ht : is_term t) by now inversion H.
    destruct (IHe0 Ht) as [e2_1 e2_2]. pose (e1' := (reify_pair (IHe He))). split.
    + exact (Let e1' e2_1).
    + exact (Let e1' e2_2).
  - assert (He : is_term e) by now inversion H. destruct (IHe He) as [e_1 e_2]. split.
    + exact e_1.
    + exact ((Label (translate_label l)) @ e_2).
Defined.
Notation "⦇ e [ H ] ⦈" := (translation e H).
Notation "*⦇ e [ H ] ⦈*" := (reify_pair (translation e H)).

Lemma translation_const k :
  ⦇source_calculus.Const k [ConstTerm k]⦈ = (Const k, Label bottom).
Proof. auto. Qed.

Lemma translation_var x :
  ⦇source_calculus.Var x [VarTerm x]⦈ = (App Fst (Var x), App Snd (Var x)).
Proof. auto. Qed.

Lemma translation_abs e (H : is_term e) :
  ⦇source_calculus.Abs e [AbsTerm e H]⦈ = (Abs *⦇e [H]⦈*, Label bottom).
Proof. auto. Qed.

Lemma translation_app e1 e2 (H1 : is_term e1) (H2 : is_term e2) :
  ⦇source_calculus.App e1 e2 [AppTerm e1 e2 H1 H2]⦈ =
     (App Fst (App (fst ⦇e1 [H1]⦈) *⦇e2 [H2]⦈*),
      (snd ⦇e1 [H1]⦈) @ (App Snd (App (fst ⦇e1 [H1]⦈) *⦇e2 [H2]⦈*))).
Proof. simpl. now destruct ⦇e1 [H1]⦈. Qed.

Lemma translation_let e1 e2 (H1 : is_term e1) (H2 : is_term e2) :
  ⦇source_calculus.Let e1 e2 [LetTerm e1 e2 H1 H2]⦈ =
    (Let *⦇e1 [H1]⦈* (fst ⦇e2 [H2]⦈), Let *⦇e1 [H1]⦈* (snd ⦇e2 [H2]⦈)).
Proof. simpl. now destruct ⦇e2 [H2]⦈. Qed.

Lemma translation_label l e (H : is_term e) :
  ⦇source_calculus.Label e l [LabelTerm e l H]⦈ = (fst ⦇e [H]⦈, (Label (translate_label l)) @ (snd ⦇e [H]⦈)).
Proof. simpl. now destruct ⦇e [H]⦈. Qed.

Notation "s → t" := (source_calculus.step s t) (at level 70).
Notation "s →@* t" := (target_calculus.star_ext s t) (at level 70).

Lemma simulation (e f : source_calculus.prefix) (He : is_term e) (Hf : is_term f) :
  e → f  -> *⦇e [He]⦈* →@* *⦇f [Hf]⦈*.
Proof.
  intros. induction H.
  - inversion He ; subst. inversion H1 ; subst. admit.
  - inversion He ; subst. admit.
  - inversion He ; subst. inversion H1 ; subst. admit.
  - inversion He ; subst. inversion Hf ; subst. admit.
  - inversion He ; subst. inversion Hf ; subst. admit.
Admitted.

End Translation.