namespace Bound

inductive Expr : Nat → Type where
  | var : {n : Nat} → Fin n → Expr n
  | number {n : Nat} : Nat → Expr n
  | string {n : Nat} : String → Expr n
  | plus {n : Nat} : Expr n → Expr n → Expr n
  | times {n : Nat} : Expr n → Expr n → Expr n
  | concatenate {n : Nat} : Expr n → Expr n → Expr n
  | length {n : Nat} : Expr n → Expr n
  | «let» {n : Nat} : Expr n → Expr n.succ → Expr n
  deriving DecidableEq, Repr

abbrev ClosedExpr : Type := Expr 0

instance {n : Nat} : ToString (Expr n) where
  toString : (Expr n) → String := 
    let rec helper {n : Nat} : Expr n → String
      | .var i => toString i
      | .number num => toString num
      | .string s => s!"\"{s}\""
      | .plus e₁ e₂ => "(" ++ helper e₁ ++ " + " ++ helper e₂ ++ ")"
      | .times e₁ e₂ => "(" ++ helper e₁ ++ " * " ++ helper e₂ ++ ")"
      | .concatenate e₁ e₂ => "(" ++ helper e₁ ++ " ++ " ++ helper e₂ ++ ")"
      | .length e => "(length " ++ helper e ++ ")"
      | .«let» e₁ e₂ => "(let 0 = " ++ helper e₁ ++ " in " ++ helper e₂ ++ ")"
    helper
