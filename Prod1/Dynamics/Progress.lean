import Prod1.Dynamics.Normal
import Prod1.Dynamics.Transition
import Prod1.Statics

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
  | .triv => Progress.done Value.triv
  | .pair e₁ e₂ =>
      match progress e₁ with
      | .step tr => Progress.step (Transition.ξ_pair₁ tr)
      | .done val₁ =>
          match progress e₂ with
          | .step tr => Progress.step (Transition.ξ_pair₂ val₁.normal tr)
          | .done val₂ => Progress.done (Value.pair val₁ val₂)
  | .proj₁ e =>
      match progress e with
      | .step tr => Progress.step (Transition.ξ_proj₁ tr)
      | .done val =>
          let .pair val₁ val₂ := val
          Progress.step (Transition.β_proj₁ val₁ val₂)
  | .proj₂ e =>
      match progress e with
      | .step tr => Progress.step (Transition.ξ_proj₂ tr)
      | .done val =>
          let .pair val₁ val₂ := val
          Progress.step (Transition.β_proj₂ val₁ val₂)
  | .abstraction _ => Progress.done Value.abstraction
  | .application e₁ e₂ =>
      match progress e₁ with
      | .step tr₁ => Progress.step (Transition.ξ_application₁ tr₁)
      | .done val₁ =>
          let .abstraction := val₁
          match progress e₂ with
          | .step tr₂ => Progress.step (Transition.ξ_application₂ Value.abstraction.normal tr₂)
          | .done val₂ => Progress.step (Transition.β_application rfl val₂.normal)
