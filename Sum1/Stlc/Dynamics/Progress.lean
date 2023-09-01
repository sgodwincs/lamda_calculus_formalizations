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
  | .nullary_case e =>
      match progress e with
      | .step tr => Progress.step (Transition.ξ_nullary_case tr)
  | .inl e =>
      match progress e with
      | .step tr => Progress.step (Transition.ξ_inl tr)
      | .done val => Progress.done (Value.inl val)
  | .inr e =>
      match progress e with
      | .step tr => Progress.step (Transition.ξ_inr tr)
      | .done val => Progress.done (Value.inr val)
  | .binary_case e eₗ eᵣ =>
      match progress e with
      | .step tr => Progress.step (Transition.ξ_binary_case tr)
      | .done val => by
          cases val with
          | inl val => exact Progress.step (Transition.β_binary_caseₗ rfl val)
          | inr val => exact Progress.step (Transition.β_binary_caseᵣ rfl val)
  | .abstraction _ => Progress.done Value.abstraction
  | .application e₁ e₂ =>
      match progress e₁ with
      | .step tr₁ => Progress.step (Transition.ξ_application₁ tr₁)
      | .done val₁ =>
          let .abstraction := val₁
          match progress e₂ with
          | .step tr₂ => Progress.step (Transition.ξ_application₂ Value.abstraction.normal tr₂)
          | .done val₂ => Progress.step (Transition.β_application rfl val₂.normal)
