Require Import source_calculus.
Require Import target_calculus.

Section Translation.

Parameter label_eq : source_calculus.label = target_calculus.label.

Definition translate_label (l : source_calculus.label) : target_calculus.label.
  rewrite <- label_eq. exact l.
Defined.

Definition reify_pair (p : term * term) : term := Pair (fst p) (snd p).

Notation "l @ m" := (App (App Join l) m) (at level 70).

Definition translation (e : source_calculus.prefix) (H : is_term e) : prod target_calculus.term target_calculus.term.
  induction e.
  - inversion H.
  - split.
    + exact (Const k).
    + exact (Label bottom).
  - split.
    + exact (App Fst (Var x)).
    + exact (App Snd (Var x)).
  - split.
    + inversion H ; subst. exact (reify_pair (IHe X)).
    + exact (Label bottom).
  - inversion H ; subst. destruct (IHe1 X) as [e1_1 e1_2]. pose (e2' := (reify_pair (IHe2 X0))). split.
    + exact (App Fst (App e1_1 e2')).
    + exact (e1_2 @ (App Snd (App e1_1 e2'))).
  - inversion H ; subst. destruct (IHe0 X0) as [e2_1 e2_2]. pose (e1' := (reify_pair (IHe X))). split.
    + exact (Let e1' e2_1).
    + exact (Let e1' e2_2).
  - inversion H ; subst. destruct (IHe X) as [e_1 e_2]. split.
    + exact e_1.
    + exact ((Label (translate_label l)) @ e_2).
Defined.

End Translation.