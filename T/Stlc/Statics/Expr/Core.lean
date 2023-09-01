import Stlc.Statics.Any
import Stlc.Statics.Context
import Stlc.Statics.Ty

namespace Statics

inductive Expr : Context → Ty → Type where
  | var
      {Γ : Context} {τ : Ty} :
      (Γ ∋ τ) →
      Expr Γ τ

  | zero
      {Γ : Context} :
      Expr Γ Ty.nat
  
  | succ
      {Γ : Context} :
      Expr Γ Ty.nat →
      Expr Γ Ty.nat

  | recursor
      {Γ : Context} {τ : Ty} :
      Expr Γ Ty.nat →
      Expr Γ τ →
      Expr (τ :: Ty.nat :: Γ) τ →
      Expr Γ τ

  | abstraction
      {Γ : Context} {τ τ' : Ty} :
      Expr (τ :: Γ) τ' → 
      Expr Γ (Ty.arrow τ τ')

  | application
      {Γ : Context} {τ τ' : Ty} :
      Expr Γ (Ty.arrow τ τ') →
      Expr Γ τ →
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
theorem cast_trans
  {Γ Δ Ψ : Context} {τ τ' τ'' : Ty} {e : Γ ⊢ τ} {e' : Δ ⊢ τ'} {e'' : Ψ ⊢ τ''}
  {hΓ : Γ = Δ} {hΓ' : Δ = Ψ} {hτ : τ = τ'} {hτ' : τ' = τ''}
  (he : e.cast hΓ hτ = e') (he' : e'.cast hΓ' hτ' = e'') :
  e.cast (hΓ.trans hΓ') (hτ.trans hτ') = e'' :=
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
theorem cast_zero
  {Γ Δ : Context} (hΓ : Γ = Δ) :
  (Expr.zero : Γ ⊢ Ty.nat).cast hΓ rfl = Expr.zero :=
by
  subst_vars
  rfl

@[simp]
theorem cast_succ
  {Γ Δ : Context} (e : Γ ⊢ Ty.nat) (hΓ : Γ = Δ) :
  (Expr.succ e : Γ ⊢ Ty.nat).cast hΓ rfl = Expr.succ (e.cast hΓ rfl) :=
by
  subst_vars
  rfl

@[simp]
theorem cast_recursor
  {Γ Δ : Context} {τ τ' : Ty} (e : Γ ⊢ Ty.nat) (e₀ : Γ ⊢ τ) (eₛ : τ :: Ty.nat :: Γ ⊢ τ) (hΓ : Γ = Δ) (hτ : τ = τ') :
  (Expr.recursor e e₀ eₛ : Γ ⊢ τ).cast hΓ hτ = Expr.recursor (e.cast hΓ rfl) (e₀.cast hΓ hτ) (eₛ.cast (congr (congr rfl hτ) (congr rfl hΓ)) hτ) :=
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

def sizeOf_gt_1 {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) : sizeOf e ≥ 1 :=
by
  cases e <;> simp_arith

end Expr
