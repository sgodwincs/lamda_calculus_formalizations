import EF.Dynamics.Normal
import EF.Dynamics.Normalization
import EF.Dynamics.Transition
import EF.Statics

open Statics

namespace Dynamics

def JudgEq {Γ : Context} {τ : Ty} (e e' : Γ ⊢ τ) : Prop := e.normal = e'.normal

notation:50 Γ " ⊢ " e " ≅ " e' " : " τ => @JudgEq Γ τ e e'

namespace JudgEq

theorem refl {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) : Γ ⊢ e ≅ e : τ := rfl

theorem symm {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ} (h : Γ ⊢ e ≅ e' : τ) : Γ ⊢ e' ≅ e : τ :=
by
  unfold JudgEq
  exact Eq.symm h

theorem trans {Γ : Context} {τ : Ty} {e₁ e₂ e₃ : Γ ⊢ τ} (h₁ : Γ ⊢ e₁ ≅ e₂ : τ) (h₂ : Γ ⊢ e₂ ≅ e₃ : τ) : Γ ⊢ e₁ ≅ e₃ : τ :=
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

theorem jeq_normal {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) : Γ ⊢ e ≅ e.normal : τ := by
  simp only [JudgEq, Expr.normal_idempotent]

theorem jeq_of_normal_eq {Γ : Context} {τ : Ty} (e e' : Γ ⊢ τ) (h : e.normal = e'.normal) : Γ ⊢ e ≅ e' : τ := by
  simp only [JudgEq]
  exact h

instance {Γ : Context} {τ : Ty} (e e' : Γ ⊢ τ) : Decidable (Γ ⊢ e ≅ e' : τ) := by
  unfold JudgEq
  match decEq e.normal e'.normal with
  | isTrue eq => rw [eq]; exact isTrue rfl
  | isFalse ne => exact isFalse (by simp_all only)
