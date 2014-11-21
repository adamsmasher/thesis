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

Fixpoint translation (e : source_calculus.prefix) : (target_calculus.term * target_calculus.term) :=
  match e with
  | source_calculus.Hole => (Const 0, Label bottom)
  | source_calculus.Const k => (Const k, Label bottom)
  | source_calculus.Var x => (App Fst (Var x), App Snd (Var x))
  | source_calculus.Abs e => (Abs (reify_pair (translation e)), Label bottom)
  | source_calculus.App e1 e2 =>
     (App Fst (App (fst (translation e1)) (reify_pair (translation e2))),
     (snd (translation e1)) @ (App Snd (App (fst (translation e1)) (reify_pair (translation e2)))))
  | source_calculus.Let e1 e2 => (Let (reify_pair (translation e1)) (fst (translation e2)),
                              Let (reify_pair (translation e1)) (snd (translation e2)))
  | source_calculus.Label e l => (fst (translation e), snd (translation e))
  end.

Notation "⦇ e ⦈" := (translation e).
Notation "*⦇ e ⦈*" := (reify_pair (translation e)).

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