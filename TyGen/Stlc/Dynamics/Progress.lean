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
  | .triv => Progress.done Value.triv
  | .pair eₗ eᵣ =>
      match progress eₗ with
      | .step tr => Progress.step (Transition.ξ_pairₗ tr)
      | .done valₗ =>
          match progress eᵣ with
          | .step tr => Progress.step (Transition.ξ_pairᵣ valₗ.normal tr)
          | .done valᵣ => Progress.done (Value.pair valₗ valᵣ)
  | .projₗ e =>
      match progress e with
      | .step tr => Progress.step (Transition.ξ_projₗ tr)
      | .done val =>
          let .pair valₗ valᵣ := val
          Progress.step (Transition.β_projₗ valₗ valᵣ)
  | .projᵣ e =>
      match progress e with
      | .step tr => Progress.step (Transition.ξ_projᵣ tr)
      | .done val =>
          let .pair valₗ valᵣ := val
          Progress.step (Transition.β_projᵣ valₗ valᵣ)
  | .nullary_case e =>
      match progress e with
      | .step tr => Progress.step (Transition.ξ_nullary_case tr)
  | .inₗ e =>
      match progress e with
      | .step tr => Progress.step (Transition.ξ_inₗ tr)
      | .done val => Progress.done (Value.inₗ val)
  | .inᵣ e =>
      match progress e with
      | .step tr => Progress.step (Transition.ξ_inᵣ tr)
      | .done val => Progress.done (Value.inᵣ val)
  | .binary_case e eₗ eᵣ =>
      match progress e with
      | .step tr => Progress.step (Transition.ξ_binary_case tr)
      | .done val => by
          cases val with
          | inₗ val => exact Progress.step (Transition.β_binary_caseₗ rfl val)
          | inᵣ val => exact Progress.step (Transition.β_binary_caseᵣ rfl val)
  | .generic_ext τ_op s s' e' e => by
      match τ_op with
      | .var =>
          cases s
          cases s'
          exact Progress.step (Transition.β_generic_ext_var e' e rfl)
      | .unit =>
          cases s
          cases s'
          exact Progress.step (Transition.β_generic_ext_unit e' e)
      | .prod τ_opₗ τ_opᵣ =>
          cases s
          cases s'
          rename_i sₗ sᵣ _ _ sₗ' sᵣ'
          exact Progress.step (Transition.β_generic_ext_prod sₗ sₗ' sᵣ sᵣ' e' e)
      | .void =>
          cases s
          cases s'
          exact Progress.step (Transition.β_generic_ext_void e' e)
      | .sum τ_opₗ τ_opᵣ =>
          cases s
          cases s'
          rename_i sₗ sᵣ _ _ sₗ' sᵣ'
          exact Progress.step (Transition.β_generic_ext_sum sₗ sₗ' sᵣ sᵣ' e' e rfl rfl)
      | .arrow τ₁ τ_op₂ =>
          cases s
          cases s'
          rename_i s _ s'
          exact Progress.step (Transition.β_generic_ext_arrow s s' e' e rfl rfl)
  | .abstraction _ => Progress.done Value.abstraction
  | .application e₁ e₂ =>
      match progress e₁ with
      | .step tr₁ => Progress.step (Transition.ξ_application₁ tr₁)
      | .done val₁ =>
          let .abstraction := val₁
          match progress e₂ with
          | .step tr₂ => Progress.step (Transition.ξ_application₂ Value.abstraction.normal tr₂)
          | .done val₂ => Progress.step (Transition.β_application rfl val₂.normal)
