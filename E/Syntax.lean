namespace Syntax

abbrev Name : Type := String

inductive Expr where
  | var : Name → Expr
  | number : Nat → Expr
  | string : String → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  | concatenate : Expr → Expr → Expr
  | length : Expr → Expr
  | «let» : Expr → Name → Expr → Expr
  deriving BEq, DecidableEq, Repr

instance : ToString Expr where
  toString : Expr → String :=
    let rec helper : Expr → String
      | .var x => toString x
      | .number num => toString num
      | .string s => s!"\"{s}\""
      | .plus e₁ e₂ => "(" ++ helper e₁ ++ " + " ++ helper e₂ ++ ")"
      | .times e₁ e₂ => "(" ++ helper e₁ ++ " * " ++ helper e₂ ++ ")"
      | .concatenate e₁ e₂ => "(" ++ helper e₁ ++ " ++ " ++ helper e₂ ++ ")"
      | .length e => "(length " ++ helper e ++ ")"
      | .«let» e₁ x e₂ => "(let " ++ toString x ++ " = " ++ helper e₁ ++ " in " ++ helper e₂ ++ ")"
    helper
