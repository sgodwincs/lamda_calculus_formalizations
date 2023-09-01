import Vect

import Stlc.Dynamics
import Stlc.Parser
import Stlc.ScopeCheck
import Stlc.Statics
import Stlc.TypeCheck

open Dynamics
open Statics

namespace Interpreter

structure Output where
  {τ : Ty}
  {e : ⊢ τ}
  val : Value e
  deriving Repr

def interpret (s : String) : Except String Output :=
  match Parser.parse s with
  | .ok e =>
      match ScopeCheck.Scoping.infer []ᵥ e with
      | .some ⟨e, _⟩ =>
          match Expr.infer [] e with
          | .some ⟨_, e⟩ =>
              let ⟨_, val'⟩ := e.eval_closed
              .ok ⟨val'⟩
          | .none => .error "type check failed"
      | .none => .error "scope check failed"
  | .error err => .error err

-- A bit of a silly example... but there isn't much that can be done with only these types.
#eval interpret "(case (inl (lambda i : void . i) : (void -> void) + void) { l⬝x -> x | r⬝y -> (lambda z : void . z) })"
