import Prod1.Statics

open Statics

namespace Syntax

abbrev Ident : Type := String

inductive Expr where
  | var : Ident → Expr
  | triv : Expr
  | pair : Expr → Expr → Expr
  | proj₁ : Expr → Expr
  | proj₂ : Expr → Expr
  | abstraction : Ident → Ty → Expr → Expr
  | application : Expr → Expr → Expr
  deriving DecidableEq, Repr
