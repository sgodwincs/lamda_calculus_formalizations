import EF.Statics

open Statics

namespace Bound

inductive Expr : Nat → Type where
  | var : {n : Nat} → Fin n → Expr n
  | number {n : Nat} : Nat → Expr n
  | string {n : Nat} : String → Expr n
  | abstraction {n : Nat} : Ty → Expr n.succ → Expr n
  | application {n : Nat} : Expr n → Expr n → Expr n
  deriving DecidableEq, Repr

abbrev ClosedExpr : Type := Expr 0
