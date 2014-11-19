Require Import Autosubst.

Section TargetCalculus.

Parameter label : Set.
Parameter bottom : label.
Parameter join : label -> label -> label.

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
| Step_app s s' t :
   step s s' -> step (App s t) (App s' t).

Notation "s → t" := (step s t) (at level 70).

Inductive step_ext : term -> term -> Prop :=
| Step s t : s → t -> step_ext s t
| Step_assoc e1 e2 e3 : step_ext ((e1 @ e2) @ e3) (e1 @ (e2 @ e3))
| Step_neutral e : step_ext (Label bottom) e.

Notation "s →@ t" := (step_ext s t) (at level 70).

Inductive star_ext : term -> term -> Prop :=
| StarR p : star_ext p p
| StarC x y z : x →@ y -> star_ext y z -> star_ext x z.
Notation "s →@* t" := (star_ext s t) (at level 70).

End TargetCalculus.