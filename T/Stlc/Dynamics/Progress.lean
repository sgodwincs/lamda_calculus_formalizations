import Stlc.Dynamics.Normal
import Stlc.Dynamics.Transition
import Stlc.Statics

open Statics

namespace Dynamics

inductive Progress {τ : Ty} (e : ⊢ τ) where
  | step
      {e' : ⊢ τ} :
      (e ⟶ e') →
      Progress e

  | done :
      Value e →
      Progress e

def _root_.Statics.Expr.progress {τ : Ty} : (e : ⊢ τ) → Progress e
  | .zero => Progress.done Value.zero
  | .succ e =>
      match progress e with
      | .step tr => Progress.step (Transition.ξ_succ tr)
      | .done val => Progress.done (Value.succ val)
  | .recursor e e₀ eₛ =>
      match progress e with
      | .step tr => Progress.step (Transition.ξ_recursor tr)
      | .done val => by
          cases val with
          | zero => exact Progress.step Transition.β_recursor₀
          | succ val => exact Progress.step (Transition.β_recursorₛ rfl val)
  | .abstraction _ => Progress.done Value.abstraction
  | .application e₁ e₂ =>
      match progress e₁ with
      | .step tr₁ => Progress.step (Transition.ξ_application₁ tr₁)
      | .done val₁ =>
          let .abstraction := val₁
          match progress e₂ with
          | .step tr₂ => Progress.step (Transition.ξ_application₂ Value.abstraction.normal tr₂)
          | .done val₂ => Progress.step (Transition.β_application rfl val₂.normal)
