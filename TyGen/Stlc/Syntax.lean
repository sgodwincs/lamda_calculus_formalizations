import Stlc.Statics

open Statics

namespace Syntax

abbrev Ident : Type := String

inductive Expr where
  | var : Ident → Expr
  | triv : Expr
  | pair : Expr → Expr → Expr
  | projₗ : Expr → Expr
  | projᵣ : Expr → Expr
  | nullary_case : Ty → Expr → Expr
  | inₗ : Ty → Ty → Expr → Expr
  | inᵣ : Ty → Ty → Expr → Expr
  | binary_case : Expr → Ident → Expr → Ident → Expr → Expr
  | generic_ext : TyOperator → Ident → Ty → Expr → Expr → Expr
  | abstraction : Ident → Ty → Expr → Expr
  | application : Expr → Expr → Expr
  deriving DecidableEq, Repr
