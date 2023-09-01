import Stlc.Statics

open Statics

namespace Syntax

abbrev Name : Type := String

inductive Expr where
  | var : Name → Expr
  | number : Nat → Expr
  | string : String → Expr
  | abstraction : Name → Ty → Expr → Expr
  | application : Expr → Expr → Expr
  deriving DecidableEq, Repr
