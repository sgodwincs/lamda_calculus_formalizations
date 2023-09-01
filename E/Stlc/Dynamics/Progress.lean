import Stlc.Bound
import Stlc.Dynamics.Normal
import Stlc.Dynamics.Transition
import Stlc.Statics

open Statics

namespace Dynamics

inductive Progress {τ : Ty} (t : ⊢ τ) where
  | step
      {t' : ⊢ τ} :
      (t ⟶ t') →
      Progress t

  | done :
      Value t →
      Progress t

def _root_.Statics.Typing.progress {τ : Ty} : (t : ⊢ τ) → Progress t
  | .number _ => Progress.done Value.number
  | .string _ => Progress.done Value.string
  | .plus t₁ t₂ =>
      match progress t₁ with
      | .step tr₁ => Progress.step (Transition.ξ_plus₁ tr₁)
      | .done val₁ =>
          let .number := val₁
          match progress t₂ with
          | .step tr₂ => Progress.step (Transition.ξ_plus₂ Value.number.normal tr₂)
          | .done val₂ => match val₂ with
            | .number => Progress.step (Transition.β_plus Value.number.normal Value.number.normal)
  | .times t₁ t₂ =>
      match progress t₁ with
      | .step tr₁ => Progress.step (Transition.ξ_times₁ tr₁)
      | .done val₁ =>
          let .number := val₁
          match progress t₂ with
          | .step tr₂ => Progress.step (Transition.ξ_times₂ Value.number.normal tr₂)
          | .done val₂ => match val₂ with
            | .number => Progress.step (Transition.β_times Value.number.normal Value.number.normal)
  | .concatenate t₁ t₂ =>
      match progress t₁ with
      | .step tr₁ => Progress.step (Transition.ξ_concatenate₁ tr₁)
      | .done val₁ =>
          let .string := val₁
          match progress t₂ with
          | .step tr₂ => Progress.step (Transition.ξ_concatenate₂ Value.string.normal tr₂)
          | .done val₂ => match val₂ with
            | .string => Progress.step (Transition.β_concatenate Value.string.normal Value.string.normal)
  | .length t =>
      match progress t with
      | .step tr => Progress.step (Transition.ξ_length tr)
      | .done val =>
          let .string := val
          Progress.step (Transition.β_length Value.string.normal)
  | .let t₁ t₂ =>
      match progress t₁ with
      | .step tr => Progress.step (Transition.ξ_let tr)
      | .done val => Progress.step (Transition.β_let rfl val.normal)
