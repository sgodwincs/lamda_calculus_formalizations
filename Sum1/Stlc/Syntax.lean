import Stlc.Statics

open Statics

namespace Syntax

abbrev Ident : Type := String

inductive Expr where
  | var : Ident → Expr
  | nullary_case : Ty → Expr → Expr
  | inl : Ty → Ty → Expr → Expr
  | inr : Ty → Ty → Expr → Expr
  | binary_case : Expr → Ident → Expr → Ident → Expr → Expr
  | abstraction : Ident → Ty → Expr → Expr
  | application : Expr → Expr → Expr
  deriving DecidableEq, Repr
