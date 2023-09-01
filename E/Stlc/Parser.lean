import Lean.Data.Parsec

import Stlc.Syntax

open Lean
open Lean.Parsec

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

private def ident : Parsec String := do
  let c ← asciiLetter
  let rest ← manyChars asciiChar
  return String.mk (c :: rest.data)

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

private def plus_term (term_core : Parsec Expr) : Parsec Expr := do
  let _ ← pchar '('
  ws
  let e₁ ← term_core
  ws
  let _ ← pchar '+'
  ws
  let e₂ ← term_core
  ws
  let _ ← pchar ')'
  return Expr.plus e₁ e₂

private def times_term (term_core : Parsec Expr) : Parsec Expr := do
  let _ ← pchar '('
  ws
  let e₁ ← term_core
  ws
  let _ ← pchar '*'
  ws
  let e₂ ← term_core
  ws
  let _ ← pchar ')'
  return Expr.times e₁ e₂

private def concatenate_term (term_core : Parsec Expr) : Parsec Expr := do
  let _ ← pchar '('
  ws
  let e₁ ← term_core
  ws
  let _ ← pstring "++"
  ws
  let e₂ ← term_core
  ws
  let _ ← pchar ')'
  return Expr.concatenate e₁ e₂

private def length_term (term_core : Parsec Expr) : Parsec Expr := do
  let _ ← pchar '('
  ws
  let _ ← pstring "length "
  ws
  let e ← term_core
  ws
  let _ ← pchar ')'
  return Expr.length e

private def let_term (term_core : Parsec Expr) : Parsec Expr := do
  let _ ← pchar '('
  ws
  let _ ← pstring "let "
  ws
  let x ← ident
  ws
  let _ ← pchar '='
  ws
  let e₁ ← term_core
  let _ ← pstring " in "
  let e₂ ← term_core
  ws
  let _ ← pchar ')'
  return Expr.let e₁ x e₂

private partial def term_core : Parsec Expr := do
  attempt var_term <|>
  attempt number_term <|>
  attempt string_term <|>
  attempt (plus_term term_core) <|>
  attempt (times_term term_core) <|>
  attempt (concatenate_term term_core) <|>
  attempt (length_term term_core) <|>
  attempt (let_term term_core)

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
