import Aesop

import EF.Statics.Any
import EF.Statics.Context
import EF.Statics.Ty

namespace Statics

inductive Expr : Context → Ty → Type where
  | var
      {Γ : Context} {τ : Ty} :
      (Γ ∋ τ) →
      Expr Γ τ

  | number
      {Γ : Context} :
      Nat →
      Expr Γ Ty.number
  
  | string
      {Γ : Context} :
      String →
      Expr Γ Ty.string
  
  | abstraction
      {Γ : Context} {τ τ' : Ty}
      (e : Expr (τ :: Γ) τ') :
      Expr Γ (Ty.arrow τ τ')

  | application
      {Γ : Context} {τ τ' : Ty}
      (e₁ : Expr Γ (Ty.arrow τ τ')) (e₂ : Expr Γ τ) :
      Expr Γ τ'
  deriving DecidableEq, Repr

notation:40 Γ " ⊢ " τ => Expr Γ τ
notation:40 "⊢ " τ => Expr [] τ

namespace Expr

def cast {Γ Δ : Context} {τ τ' : Ty} (e : Γ ⊢ τ) (hΓ : Γ = Δ) (hτ : τ = τ') : Δ ⊢ τ' := hΓ ▸ hτ ▸ e

@[simp]
theorem cast_rfl_rfl {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) : e.cast rfl rfl = e := rfl

@[simp]
theorem cast_cast
  {Γ Δ Ψ : Context} {τ τ' τ'' : Ty} (e : Γ ⊢ τ) (hΓ : Γ = Δ) (hΓ' : Δ = Ψ) (hτ : τ = τ') (hτ' : τ' = τ'') :
  (e.cast hΓ hτ).cast hΓ' hτ' = e.cast (hΓ.trans hΓ') (hτ.trans hτ') :=
by
  subst_vars
  rfl

@[simp]
theorem cast_var
  {Γ Δ : Context} {τ τ' : Ty} (a : Γ ∋ τ) (hΓ : Γ = Δ) (hτ : τ = τ') :
  (Expr.var a : Γ ⊢ τ).cast hΓ hτ = Expr.var (a.cast hΓ hτ) :=
by
  subst_vars
  rfl

@[simp]
theorem cast_number
  {Γ Δ : Context} (num : Nat) (hΓ : Γ = Δ) :
  (Expr.number num : Γ ⊢ Ty.number).cast hΓ rfl = Expr.number num :=
by
  subst_vars
  rfl

@[simp]
theorem cast_string
  {Γ Δ : Context} (s : String) (hΓ : Γ = Δ) :
  (Expr.string s : Γ ⊢ Ty.string).cast hΓ rfl = Expr.string s :=
by
  subst_vars
  rfl

@[simp]
theorem cast_abstraction
  {Γ Δ : Context} {τ₁ τ₂ τ₂' : Ty} (e : τ₁ :: Γ ⊢ τ₂) (hΓ : Γ = Δ) (hτ₂ : τ₂ = τ₂') :
  (Expr.abstraction e : Γ ⊢ Ty.arrow τ₁ τ₂).cast hΓ (hτ₂ ▸ rfl) = Expr.abstraction (e.cast (congr rfl hΓ) hτ₂) :=
by
  subst_vars
  rfl

@[simp]
theorem cast_application
  {Γ Δ : Context} {τ₁ τ₁' τ₂ τ₂' : Ty} (e₁ : Γ ⊢ Ty.arrow τ₁ τ₂) (e₂ : Γ ⊢ τ₁) (hΓ : Γ = Δ) (hτ₁ : τ₁ = τ₁') (hτ₂ : τ₂ = τ₂') :
  (Expr.application e₁ e₂ : Γ ⊢ τ₂).cast hΓ hτ₂ = Expr.application (e₁.cast hΓ (hτ₁ ▸ hτ₂ ▸ rfl)) (e₂.cast hΓ hτ₁) :=
by
  subst_vars
  rfl

end Expr
