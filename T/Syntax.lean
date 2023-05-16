import T.Statics

open Statics

namespace Syntax

abbrev Ident : Type := String

inductive Expr where
  | var : Ident → Expr
  | zero : Expr
  | succ : Expr → Expr
  | recursor : Expr → Expr → Ident → Ident → Expr → Expr
  | abstraction : Ident → Ty → Expr → Expr
  | application : Expr → Expr → Expr
  deriving DecidableEq, Repr
