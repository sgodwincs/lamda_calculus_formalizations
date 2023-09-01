import Stlc.Dynamics.Normal
import Stlc.Dynamics.Normalization
import Stlc.Dynamics.Transition
import Stlc.Statics

open Statics

namespace Dynamics

def JudgEq {Γ : Context} {τ : Ty} (t t' : Γ ⊢ τ) : Prop := t.normal = t'.normal

notation:50 Γ " ⊢ " t " ≅ " t' " : " τ => @JudgEq Γ τ t t'

namespace JudgEq

theorem refl {Γ : Context} {τ : Ty} (t : Γ ⊢ τ) : Γ ⊢ t ≅ t : τ := rfl

theorem symm {Γ : Context} {τ : Ty} {t t' : Γ ⊢ τ} (h : Γ ⊢ t ≅ t' : τ) : Γ ⊢ t' ≅ t : τ :=
by
  unfold JudgEq
  exact Eq.symm h

theorem trans {Γ : Context} {τ : Ty} {t₁ t₂ t₃ : Γ ⊢ τ} (h₁ : Γ ⊢ t₁ ≅ t₂ : τ) (h₂ : Γ ⊢ t₂ ≅ t₃ : τ) : Γ ⊢ t₁ ≅ t₃ : τ :=
by
  unfold JudgEq
  rw [h₁, h₂]

theorem eqv {Γ : Context} {τ : Ty} : Equivalence (@JudgEq Γ τ) := {
    refl := refl,
    symm := symm,
    trans := trans
  }

instance {Γ : Context} {τ : Ty} : Setoid (Γ ⊢ τ) where
  r := JudgEq
  iseqv := eqv

theorem jeq_normal {Γ : Context} {τ : Ty} (t : Γ ⊢ τ) : Γ ⊢ t ≅ t.normal : τ := by
  simp only [JudgEq, Typing.normal_idempotent]

theorem jeq_of_normal_eq {Γ : Context} {τ : Ty} (t t' : Γ ⊢ τ) (h : t.normal = t'.normal) : Γ ⊢ t ≅ t' : τ := by
  simp only [JudgEq]
  exact h

instance {Γ : Context} {τ : Ty} (t t' : Γ ⊢ τ) : Decidable (Γ ⊢ t ≅ t' : τ) := by
  unfold JudgEq
  match decEq t.normal t'.normal with
  | isTrue eq => rw [eq]; exact isTrue rfl
  | isFalse ne => exact isFalse (by simp_all only)
