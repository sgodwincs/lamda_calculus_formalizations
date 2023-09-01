import Stlc.Statics

open Statics

namespace Bound

inductive Expr : Nat → Type where
  | var {n : Nat} : Fin n → Expr n
  | nullary_case {n : Nat} : Ty → Expr n → Expr n
  | inl {n : Nat} : Ty → Ty → Expr n → Expr n
  | inr {n : Nat} : Ty → Ty → Expr n → Expr n
  | binary_case {n : Nat} : Expr n → Expr n.succ → Expr n.succ → Expr n
  | abstraction {n : Nat} : Ty → Expr n.succ → Expr n
  | application {n : Nat} : Expr n → Expr n → Expr n
  deriving DecidableEq, Repr

abbrev ClosedExpr : Type := Expr 0
