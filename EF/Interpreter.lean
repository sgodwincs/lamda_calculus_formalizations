import Vector

import EF.Dynamics
import EF.Parser
import EF.ScopeCheck
import EF.Statics
import EF.TypeCheck

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

#eval interpret "((lambda x : string . x) \"hello\")"
