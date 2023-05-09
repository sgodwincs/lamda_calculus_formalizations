import Lean.Data.Parsec

import EF.Statics
import EF.Syntax

open Lean (Parsec)
open Lean.Parsec

open Statics (Ty)
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

private def number_ty : Parsec Ty := do
  let _ ← pstring "number"
  return Ty.number
  
private def string_ty : Parsec Ty := do
  let _ ← pstring "string"
  return Ty.string

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
  attempt number_ty <|>
  attempt string_ty <|>
  attempt (arrow_ty ty)

private def var_term : Parsec Expr := do
  let var ← ident
  return Expr.var var

private def number_term : Parsec Expr := do
  let num ← nat_maybe_zero
  return Expr.number num

private def string_term : Parsec Expr := do
  let _ ← pchar '"'
  ws
  let s ← manyChars asciiChar
  ws
  let _ ← pchar '"'
  return Expr.string s

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
  attempt number_term <|>
  attempt string_term <|>
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
