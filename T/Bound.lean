import T.Statics

open Statics

namespace Bound

inductive Expr : Nat → Type where
  | var : {n : Nat} → Fin n → Expr n
  | zero {n : Nat} : Expr n
  | succ {n : Nat} : Expr n → Expr n
  | recursor {n : Nat} : Expr n → Expr n → Expr n.succ.succ → Expr n
  | abstraction {n : Nat} : Ty → Expr n.succ → Expr n
  | application {n : Nat} : Expr n → Expr n → Expr n
  deriving DecidableEq, Repr

abbrev ClosedExpr : Type := Expr 0
