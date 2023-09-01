import Vector

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
  {t : ⊢ τ}
  val : Value t
  deriving Repr

def interpret (s : String) : Except String Output :=
  match Parser.parse s with
  | .ok e =>
      match ScopeCheck.Scoping.infer Vector.nil e with
      | .some ⟨e, _⟩ =>
          match Typing.infer [] e with
          | .some ⟨_, t⟩ =>
              let ⟨_, val'⟩ := t.eval_closed
              .ok ⟨val'⟩
          | .none => .error "type check failed"
      | .none => .error "scope check failed"
  | .error err => .error err

#eval interpret "(let x = (\"abc\" ++ \"def\") in ((length x) + 5))"
