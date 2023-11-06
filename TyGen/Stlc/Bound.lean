import Stlc.Statics

open Statics

namespace Bound

inductive Expr : Nat → Type where
  | var : {n : Nat} → Fin n → Expr n
  | triv {n : Nat} : Expr n
  | pair {n : Nat} : Expr n → Expr n → Expr n
  | projₗ {n : Nat} : Expr n → Expr n
  | projᵣ {n : Nat} : Expr n → Expr n
  | nullary_case {n : Nat} : Ty → Expr n → Expr n
  | inₗ {n : Nat} : Ty → Ty → Expr n → Expr n
  | inᵣ {n : Nat} : Ty → Ty → Expr n → Expr n
  | binary_case {n : Nat} : Expr n → Expr n.succ → Expr n.succ → Expr n
  | generic_ext {n : Nat} : TyOperator → Ty → Expr n.succ → Expr n → Expr n
  | abstraction {n : Nat} : Ty → Expr n.succ → Expr n
  | application {n : Nat} : Expr n → Expr n → Expr n
  deriving DecidableEq, Repr

abbrev ClosedExpr : Type := Expr 0
