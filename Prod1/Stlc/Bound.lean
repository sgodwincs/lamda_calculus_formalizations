import Stlc.Statics

open Statics

namespace Bound

inductive Expr : Nat → Type where
  | var : {n : Nat} → Fin n → Expr n
  | triv {n : Nat} : Expr n
  | pair {n : Nat} : Expr n → Expr n → Expr n
  | proj₁ {n : Nat} : Expr n → Expr n
  | proj₂ {n : Nat} : Expr n → Expr n
  | abstraction {n : Nat} : Ty → Expr n.succ → Expr n
  | application {n : Nat} : Expr n → Expr n → Expr n
  deriving DecidableEq, Repr

abbrev ClosedExpr : Type := Expr 0
