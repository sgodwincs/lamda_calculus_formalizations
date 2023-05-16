import T.Statics.Context

namespace Statics

inductive Any : Context → Ty → Type where
  | here {Γ : Context} {τ : Ty} : Any (τ :: Γ) τ
  | there {Γ : Context} {τ τ' : Ty} : Any Γ τ' → Any (τ :: Γ) τ'
  deriving DecidableEq, Repr

notation:50 Γ " ∋ " τ => Any Γ τ

namespace Any

def cast {Γ Δ : Context} {τ τ' : Ty} (a : Γ ∋ τ) (hΓ : Γ = Δ) (hτ : τ = τ') : Δ ∋ τ' := hΓ ▸ hτ ▸ a

@[simp]
theorem cast_rfl_rfl {Γ : Context} {τ : Ty} (a : Γ ∋ τ) : a.cast rfl rfl = a := rfl

@[simp]
theorem cast_trans
  {Γ Δ Ψ : Context} {τ τ' τ'' : Ty} {a : Γ ∋ τ} {a' : Δ ∋ τ'} {a'' : Ψ ∋ τ''}
  {hΓ : Γ = Δ} {hΓ' : Δ = Ψ} {hτ : τ = τ'} {hτ' : τ' = τ''}
  (ha : a.cast hΓ hτ = a') (ha' : a'.cast hΓ' hτ' = a'') :
  a.cast (hΓ.trans hΓ') (hτ.trans hτ') = a'' :=
by
  subst_vars
  rfl

@[simp]
theorem cast_cast
  {Γ Δ Ψ : Context} {τ τ' τ'' : Ty} (a : Γ ∋ τ) (hΓ : Γ = Δ) (hΓ' : Δ = Ψ) (hτ : τ = τ') (hτ' : τ' = τ'') :
  (a.cast hΓ hτ).cast hΓ' hτ' = a.cast (hΓ.trans hΓ') (hτ.trans hτ') :=
by
  subst_vars
  rfl

@[simp]
theorem cast_here
  {Γ Δ : Context} {τ τ' : Ty} (hΓ : Γ = Δ) (hτ : τ = τ') :
  (Any.here : τ :: Γ ∋ τ).cast (congr (congr rfl hτ) hΓ) hτ = (Any.here : τ' :: Δ ∋ τ') :=
by
  subst_vars
  rfl

@[simp]
theorem cast_there
  {Γ Δ : Context} {τ₁ τ₂ τ₂' : Ty} (a : Γ ∋ τ₂) (hΓ : Γ = Δ) (hτ : τ₂ = τ₂') :
  (Any.there a : τ₁ :: Γ ∋ τ₂).cast (congr rfl hΓ) hτ = Any.there (a.cast hΓ hτ) :=
by
  subst_vars
  rfl

structure FromFin (Γ : Context) where
  {τ : Ty}
  a : Γ ∋ τ

def from_fin : (Γ : Context) → Fin Γ.length → FromFin Γ
  | _ :: _, ⟨0, _⟩ => ⟨Any.here⟩
  | _ :: Γ, ⟨n + 1, lt⟩ => ⟨Any.there (from_fin Γ ⟨n, Nat.lt_of_succ_lt_succ lt⟩).a⟩  

def to_fin {Γ : Context} {τ : Ty} : (Γ ∋ τ) → Fin Γ.length
  | .here => ⟨0, Nat.zero_lt_succ _⟩
  | .there a => a.to_fin.succ

@[simp]
theorem to_from_fin_inverse {Γ : Context} {τ : Ty} (a : Γ ∋ τ) : from_fin Γ (to_fin a) = ⟨a⟩ :=
  match a with
  | here => rfl
  | @there Γ τ _ a => by
      show FromFin.mk (there (from_fin Γ { val := (to_fin a).val, isLt := (_ : (to_fin a).val < List.length Γ) }).a) = _
      rw [to_from_fin_inverse _]

@[simp]
theorem from_to_fin_inverse (Γ : Context) (i : Fin Γ.length) : to_fin (from_fin Γ i).2 = i := by
  match Γ, i with
  | _ :: _, ⟨0, _⟩ => rfl
  | _ :: Γ, ⟨n + 1, lt⟩ =>
      show Fin.succ (to_fin (from_fin Γ { val := n, isLt := (_ : n < List.length Γ) }).a) = _
      rw [from_to_fin_inverse _ _]
      dsimp only [Fin.succ]

end Any
