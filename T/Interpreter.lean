import Vector

import T.Dynamics
import T.Parser
import T.ScopeCheck
import T.Statics
import T.TypeCheck

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
      match ScopeCheck.Scoping.infer Vector.nil e with
      | .some ⟨e, _⟩ =>
          match Expr.infer [] e with
          | .some ⟨_, e⟩ =>
              let ⟨_, val'⟩ := e.eval_closed
              .ok ⟨val'⟩
          | .none => .error "type check failed"
      | .none => .error "scope check failed"
  | .error err => .error err

-- Multiply by 2
#eval interpret "((lambda n : nat . (rec n { z => zero | s(p) with r => (succ (succ r)) })) (succ (succ zero)))"
