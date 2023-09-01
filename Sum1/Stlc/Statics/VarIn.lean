import Stlc.Statics.Context
import Stlc.Statics.Ty

namespace Statics

inductive VarIn : Context → Ty → Type where
  | here {Γ : Context} {τ : Ty} : VarIn (τ :: Γ) τ
  | there {Γ : Context} {τ₁ τ₂ : Ty} : VarIn Γ τ₂ → VarIn (τ₁ :: Γ) τ₂
  deriving DecidableEq, Repr

notation:50 Γ " ∋ " τ => VarIn Γ τ

namespace VarIn

def cast {Γ Γ' : Context} {τ τ' : Ty} (a : Γ ∋ τ) (hΓ : Γ = Γ') (hτ : τ = τ') : Γ' ∋ τ' := hΓ ▸ hτ ▸ a

@[simp]
theorem cast_rfl_rfl {Γ : Context} {τ : Ty} (a : Γ ∋ τ) : a.cast rfl rfl = a := rfl

@[simp]
theorem cast_trans
  {Γ Γ' Γ'' : Context} {τ τ' τ'' : Ty} {a : Γ ∋ τ} {a' : Γ' ∋ τ'} {a'' : Γ'' ∋ τ''}
  {hΓ : Γ = Γ'} {hΓ' : Γ' = Γ''} {hτ : τ = τ'} {hτ' : τ' = τ''}
  (ha : a.cast hΓ hτ = a') (ha' : a'.cast hΓ' hτ' = a'') :
  a.cast (hΓ.trans hΓ') (hτ.trans hτ') = a''
:= by
  subst_vars
  rfl

@[simp]
theorem cast_cast
  {Γ Γ' Γ'' : Context} {τ τ' τ'' : Ty}
  (a : Γ ∋ τ) (hΓ : Γ = Γ') (hΓ' : Γ' = Γ'') (hτ : τ = τ') (hτ' : τ' = τ'') :
  (a.cast hΓ hτ).cast hΓ' hτ' = a.cast (hΓ.trans hΓ') (hτ.trans hτ')
:= by
  subst_vars
  rfl

@[simp]
theorem cast_here
  {Γ Γ' : Context} {τ τ' : Ty}
  (hΓ : Γ = Γ') (hτ : τ = τ') :
  (here : τ :: Γ ∋ τ).cast (congr (hτ ▸ rfl) hΓ) hτ = (here : τ' :: Γ' ∋ τ')
:= by
  subst_vars
  rfl

@[simp]
theorem cast_there
  {Γ Γ' : Context} {τ₁ τ₂ τ₂' : Ty}
  (a : Γ ∋ τ₂) (hΓ : Γ = Γ') (hτ : τ₂ = τ₂') :
  (there a : τ₁ :: Γ ∋ τ₂).cast (congr rfl hΓ) hτ = there (a.cast hΓ hτ)
:= by
  subst_vars
  rfl

structure FromFin (Γ : Context) where
  {τ : Ty}
  a : Γ ∋ τ

def from_fin : (Γ : Context) → Fin Γ.length → FromFin Γ
  | _ :: _, ⟨0, _⟩ => ⟨here⟩
  | _ :: Γ, ⟨n + 1, lt⟩ => ⟨there (from_fin Γ ⟨n, Nat.lt_of_succ_lt_succ lt⟩).a⟩  

def to_fin {Γ : Context} {τ : Ty} : (Γ ∋ τ) → Fin Γ.length
  | here => ⟨0, Nat.zero_lt_succ _⟩
  | there a => a.to_fin.succ

@[simp]
theorem to_from_fin_inverse {Γ : Context} {τ : Ty} (a : Γ ∋ τ) : from_fin Γ (to_fin a) = ⟨a⟩ :=
  match a with
  | here => rfl
  | there a => by
      show FromFin.mk (there (from_fin _ ⟨(to_fin a).val, _⟩).a) = _
      rw [to_from_fin_inverse]

@[simp]
theorem from_to_fin_inverse (Γ : Context) (i : Fin Γ.length) : to_fin (from_fin Γ i).2 = i :=
  match Γ, i with
  | _ :: _, ⟨0, _⟩ => rfl
  | _ :: Γ, ⟨n + 1, lt⟩ => by
      show Fin.succ (to_fin (from_fin Γ ⟨n, _⟩).a) = _
      rw [from_to_fin_inverse _ _]
      dsimp only [Fin.succ]

end VarIn
