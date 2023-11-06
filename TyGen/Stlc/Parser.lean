import Lean.Data.Parsec

import Stlc.Statics
import Stlc.Syntax

open Lean (Parsec)
open Lean.Parsec

open Statics (Ty TyOperator)
open Syntax

namespace Parser

private partial def nat_core (acc digits : Nat) : Parsec (Nat × Nat) := do
  let some c ← peek? | return (acc, digits)
  if '0' ≤ c ∧ c ≤ '9' then
    skip
    let acc' := 10 * acc + (c.val.toNat - '0'.val.toNat)
    nat_core acc' (digits + 1)
  else
    return (acc, digits)

private def lookahead (p : Char → Prop) (desc : String) [DecidablePred p] : Parsec Unit := do
  let c ← peek!
  if p c then
    return ()
  else
    fail <| "expected " ++ desc

private def nat_num_digits : Parsec (Nat × Nat) := do
  lookahead (fun c => '0' ≤ c ∧ c ≤ '9') "digit"
  nat_core 0 0

def nat_maybe_zero : Parsec Nat := do
  let (n, _) ← nat_num_digits
  return n

private def asciiChar : Parsec Char := asciiLetter <|> digit

private def ws1 : Parsec Unit := attempt do
  let c ← anyChar
  if c = '\u0009' ∨ c = '\u000a' ∨ c = '\u000d' ∨ c = '\u0020' then
    ws
    pure ()
  else
    fail s!"expected whitespace"

private def ident : Parsec String := do
  let c ← asciiLetter
  let rest ← manyChars asciiChar
  return String.mk (c :: rest.data)

private def unit_ty : Parsec Ty := do
  let _ ← pstring "unit"
  return Ty.unit

private def prod_ty (ty_core : Parsec Ty) : Parsec Ty := do
  let _ ← pchar '('
  ws
  let ty₁ ← ty_core
  ws
  let _ ← pchar '×'
  ws
  let ty₂ ← ty_core
  ws
  let _ ← pchar ')'
  return Ty.prod ty₁ ty₂

private def void_ty : Parsec Ty := do
  let _ ← pstring "void"
  return Ty.void

private def sum_ty (ty_core : Parsec Ty) : Parsec Ty := do
  let _ ← pchar '('
  ws
  let ty₁ ← ty_core
  ws
  let _ ← pchar '+'
  ws
  let ty₂ ← ty_core
  ws
  let _ ← pchar ')'
  return Ty.sum ty₁ ty₂

private def arrow_ty (ty_core : Parsec Ty) : Parsec Ty := do
  let _ ← pchar '('
  ws
  let ty₁ ← ty_core
  ws
  let _ ← pstring "->"
  ws
  let ty₂ ← ty_core
  ws
  let _ ← pchar ')'
  return Ty.arrow ty₁ ty₂

private partial def ty : Parsec Ty := do
  attempt unit_ty <|>
  attempt (prod_ty ty) <|>
  attempt void_ty <|>
  attempt (sum_ty ty) <|>
  attempt (arrow_ty ty)

private def var_ty_operator : Parsec TyOperator := do
  let _ ← pchar 't'
  return TyOperator.var

private def unit_ty_operator : Parsec TyOperator := do
  let _ ← pstring "unit"
  return TyOperator.unit

private def prod_ty_operator (τ_op_core : Parsec TyOperator) := do
  let _ ← pchar '('
  ws
  let τ_opₗ ← τ_op_core
  ws
  let _ ← pchar '×'
  ws
  let τ_opᵣ ← τ_op_core
  ws
  let _ ← pchar ')'
  return TyOperator.prod τ_opₗ τ_opᵣ

private def void_ty_operator : Parsec TyOperator := do
  let _ ← pstring "void"
  return TyOperator.void

private def sum_ty_operator (τ_op_core : Parsec TyOperator) := do
  let _ ← pchar '('
  ws
  let τ_opₗ ← τ_op_core
  ws
  let _ ← pchar '+'
  ws
  let τ_opᵣ ← τ_op_core
  ws
  let _ ← pchar ')'
  return TyOperator.sum τ_opₗ τ_opᵣ

private def arrow_ty_operator (τ_op_core : Parsec TyOperator) := do
  let _ ← pchar '('
  ws
  let τ₁ ← ty
  ws
  let _ ← pstring "->"
  ws
  let τ_op₂ ← τ_op_core
  ws
  let _ ← pchar ')'
  return TyOperator.arrow τ₁ τ_op₂

private partial def ty_operator : Parsec TyOperator := do
  attempt var_ty_operator <|>
  attempt unit_ty_operator <|>
  attempt (prod_ty_operator ty_operator) <|>
  attempt void_ty_operator <|>
  attempt (sum_ty_operator ty_operator) <|>
  attempt (arrow_ty_operator ty_operator)

private def ty_operator_binding : Parsec TyOperator := do
  let _ ← pchar 't'
  ws
  let _ ← pchar '.'
  ws
  ty_operator

private def var_term : Parsec Expr := do
  let var ← ident
  return Expr.var var

private def triv_term : Parsec Expr := do
  let _ ← pstring "⟨⟩"
  return Expr.triv

private def pair_term (term_core : Parsec Expr) := do
  let _ ← pchar '⟨'
  ws
  let e₁ ← term_core
  ws
  let _ ← pchar ','
  ws
  let e₂ ← term_core
  ws
  let _ ← pchar '⟩'
  return Expr.pair e₁ e₂

private def projₗ_term (term_core : Parsec Expr) : Parsec Expr := do
  let _ ← pchar '('
  ws
  let _ ← pstring "projₗ"
  ws1
  let e ← term_core
  ws
  let _ ← pchar ')'
  return Expr.projₗ e

private def projᵣ_term (term_core : Parsec Expr) : Parsec Expr := do
  let _ ← pchar '('
  ws
  let _ ← pstring "projᵣ"
  ws1
  let e ← term_core
  ws
  let _ ← pchar ')'
  return Expr.projᵣ e

private def nullary_case_term (term_core : Parsec Expr) : Parsec Expr := do
  let _ ← pchar '('
  ws
  let _ ← pstring "case"
  ws1
  let e ← term_core
  ws
  let _ ← pstring "{}"
  ws
  let _ ← pchar ':'
  ws
  let ty ← ty
  let _ ← pchar ')'
  return Expr.nullary_case ty e

private def inₗ_term (term_core : Parsec Expr) : Parsec Expr := do
  let _ ← pchar '('
  ws
  let _ ← pstring "inₗ"
  ws1
  let e ← term_core
  ws
  let _ ← pchar ':'
  ws
  let ty₁ ← ty
  ws
  let _ ← pchar '+'
  ws
  let ty₂ ← ty
  ws
  let _ ← pchar ')'
  return Expr.inₗ ty₁ ty₂ e

private def inᵣ_term (term_core : Parsec Expr) : Parsec Expr := do
  let _ ← pchar '('
  ws
  let _ ← pstring "inᵣ"
  ws1
  let e ← term_core
  ws
  let _ ← pchar ':'
  ws
  let ty₁ ← ty
  ws
  let _ ← pchar '+'
  ws
  let ty₂ ← ty
  ws
  let _ ← pchar ')'
  return Expr.inᵣ ty₁ ty₂ e

private def binary_case_term (term_core : Parsec Expr) : Parsec Expr := do
  let _ ← pchar '('
  ws
  let _ ← pstring "case"
  ws1
  let e ← term_core
  ws
  let _ ← pstring "{"
  ws
  let _ ← pchar 'l'
  ws
  let _ ← pchar '⬝'
  ws
  let x ← ident
  ws
  let _ ← pstring "->"
  ws
  let eₗ ← term_core
  ws
  let _ ← pchar '|'
  ws
  let _ ← pchar 'r'
  ws
  let _ ← pchar '⬝'
  ws
  let y ← ident
  ws
  let _ ← pstring "->"
  ws
  let eᵣ ← term_core
  ws
  let _ ← pstring "}"
  ws
  let _ ← pchar ')'
  return Expr.binary_case e x eₗ y eᵣ

private def generic_ext (term_core : Parsec Expr) : Parsec Expr := do
  let _ ← pchar '('
  ws
  let _ ← pstring "map"
  ws
  let _ ← pchar '{'
  ws
  let τ_op ← ty_operator_binding
  ws
  let _ ← pchar '}'
  ws
  let _ ← pchar '('
  ws
  let x ← ident
  ws
  let _ ← pchar ':'
  ws
  let τ ← ty
  ws
  let _ ← pchar '.'
  ws
  let e' ← term_core
  ws
  let _ ← pchar ')'
  ws
  let _ ← pchar '('
  ws
  let e ← term_core
  ws
  let _ ← pchar ')'
  ws
  let _ ← pchar ')'
  return Expr.generic_ext τ_op x τ e' e

private def abstraction_term (term_core : Parsec Expr) : Parsec Expr := do
  let _ ← pchar '('
  ws
  let _ ← pstring "lambda"
  ws1
  let x ← ident
  ws
  let _ ← pchar ':'
  ws
  let ty ← ty
  ws
  let _ ← pchar '.'
  ws
  let e ← term_core
  ws
  let _ ← pchar ')'
  return Expr.abstraction x ty e

private def application_term (term_core : Parsec Expr) : Parsec Expr := do
  let _ ← pchar '('
  ws
  let e₁ ← term_core
  ws1
  let e₂ ← term_core
  ws
  let _ ← pchar ')'
  return Expr.application e₁ e₂

private partial def term_core : Parsec Expr := do
  attempt var_term <|>
  attempt triv_term <|>
  attempt (pair_term term_core) <|>
  attempt (projₗ_term term_core) <|>
  attempt (projᵣ_term term_core) <|>
  attempt (nullary_case_term term_core) <|>
  attempt (inₗ_term term_core) <|>
  attempt (inᵣ_term term_core) <|>
  attempt (binary_case_term term_core) <|>
  attempt (generic_ext term_core) <|>
  attempt (abstraction_term term_core) <|>
  attempt (application_term term_core)

private def term : Parsec Expr := do
  ws
  let res ← term_core
  ws
  eof
  return res

def parse (s : String) : Except String Expr :=
  match term s.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok res
  | Parsec.ParseResult.error it err => Except.error s!"offset {repr it.i.byteIdx}: {err}"
