import E.Statics.Context

namespace Statics

inductive Any : Context → Ty → Type where
  | here {Γ : Context} {τ : Ty} : Any (τ :: Γ) τ
  | there {Γ : Context} {τ₁ τ₂ : Ty} : Any Γ τ₂ → Any (τ₁ :: Γ) τ₂
  deriving DecidableEq, Repr

notation:40 Γ " ∋ " τ => Any Γ τ

namespace Any

def from_fin : (Γ : Context) → Fin Γ.length → Σ τ : Ty, Γ ∋ τ
  | τ :: _, ⟨0, _⟩ => ⟨τ, Any.here⟩
  | _ :: Γ, ⟨n + 1, lt⟩ =>
      let ⟨τ, a⟩ := from_fin Γ ⟨n, Nat.lt_of_succ_lt_succ lt⟩  
      ⟨τ, Any.there a⟩

def to_fin {Γ : Context} {τ : Ty} : (Γ ∋ τ) → Fin Γ.length
  | .here => ⟨0, Nat.zero_lt_succ _⟩
  | .there a => a.to_fin.succ

@[simp]
theorem to_from_fin_inverse {Γ : Context} {τ : Ty} (a : Γ ∋ τ) : from_fin Γ (to_fin a) = ⟨τ, a⟩ :=
  match a with
  | here => rfl
  | @there Γ τ₁ _ a => by
      show (let ⟨τ, a⟩ := from_fin Γ ⟨to_fin a, _⟩; (⟨τ, Any.there a⟩ : Sigma _)) = _
      rw [to_from_fin_inverse a]

@[simp]
theorem from_to_fin_inverse (Γ : Context) (i : Fin Γ.length) : to_fin (from_fin Γ i).2 = i := by
  match Γ, i with
  | τ :: _, ⟨0, _⟩ => rfl
  | τ :: Γ, ⟨n + 1, lt⟩ =>
      show Fin.succ (to_fin (from_fin Γ { val := n, isLt := (_ : n < List.length Γ) }).snd) = _
      rw [from_to_fin_inverse Γ ⟨n, Nat.lt_of_succ_lt_succ lt⟩]
      simp only [Fin.succ]
