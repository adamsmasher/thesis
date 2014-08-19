(* based on Pottier and Conchon, Information
    Flow Inference for Free *)

Require Import Autosubst.

Section SourceCalculus.

(* as in the original paper, for now we leave
     the set of labels entirely abstract *)

Parameter label : Set.

Inductive term : Type :=
| Const (k : nat)
| Var (x : var)
| Abs (s : {bind term})
| App (s t : term)
| Let (s : term) (t : {bind term})
| Label (s : term) (l : label).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_type : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Defined.

(* notion of contexts taken from Proving ML Type Soundness Within Coq by Catherine Dubois *)
(* for now our contexts are abstract *)
Definition eval_ctx := term -> term.
Parameter is_context : eval_ctx -> Prop.

Inductive step : term -> term -> Prop :=
| Step_beta (s t : term) :
   step (App (Abs s) t) s.[t/]
| Step_let (s t : term) :
   step (Let s t) t.[s/]
| Step_lift (s t : term) (l : label) :
   step (App (Label s l) t) (Label (App s t) l)
| Step_context (s1 s2 : term) (E : eval_ctx) :
   is_context E -> step s1 s2 ->
   step (E s1) (E s2).

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
