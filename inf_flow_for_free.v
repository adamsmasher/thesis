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

Inductive star : prefix -> prefix -> Prop :=
| StarR p : star p p
| StarC x y z : step x y -> star y z -> star x z.

Fixpoint prefix_match (p1 p2 : prefix) : Prop :=
  match p1, p2 with
  | Hole, _ => True
  | Const k1, Const k2 => k1 = k2
  | Var x1, Var x2 => x1 = x2
  | Abs s1, Abs s2 => prefix_match s1 s2
  | App s1 t1, App s2 t2 => prefix_match s1 s2 /\ prefix_match t1 t2
  | Let s1 t1, Let s2 t2 => prefix_match s1 s2 /\ prefix_match t1 t2
  | Label s1 l1, Label s2 l2 => prefix_match s1 s2 /\ l1 = l2
  | _, _ => False
  end.

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
