import Stlc.Statics.Context
import Stlc.Statics.Ty
import Stlc.Statics.VarIn

namespace Statics

inductive Expr : Context → Ty → Type where
  | var
      {Γ : Context} {τ : Ty} :
      (Γ ∋ τ) →
      Expr Γ τ
  
  | nullary_case
      {Γ : Context} {τ : Ty} :
      Expr Γ Ty.void →
      Expr Γ τ
  
  | inl
      {Γ : Context} {τₗ τᵣ : Ty} :
      Expr Γ τₗ →
      Expr Γ (Ty.sum τₗ τᵣ)
  
  | inr
      {Γ : Context} {τₗ τᵣ : Ty} :
      Expr Γ τᵣ →
      Expr Γ (Ty.sum τₗ τᵣ)
  
  | binary_case
      {Γ : Context} {τ τₗ τᵣ : Ty} :
      Expr Γ (Ty.sum τₗ τᵣ) →
      Expr (τₗ :: Γ) τ →
      Expr (τᵣ :: Γ) τ →
      Expr Γ τ

  | abstraction
      {Γ : Context} {τ₁ τ₂ : Ty} :
      Expr (τ₁ :: Γ) τ₂ → 
      Expr Γ (Ty.arrow τ₁ τ₂)

  | application
      {Γ : Context} {τ₁ τ₂ : Ty} :
      Expr Γ (Ty.arrow τ₁ τ₂) →
      Expr Γ τ₁ →
      Expr Γ τ₂
  deriving DecidableEq, Repr

notation:40 Γ " ⊢ " τ => Expr Γ τ
notation:40 "⊢ " τ => Expr [] τ

namespace Expr

abbrev cast {Γ Γ' : Context} {τ τ' : Ty} (e : Γ ⊢ τ) (hΓ : Γ = Γ') (hτ : τ = τ') : Γ' ⊢ τ' := hΓ ▸ hτ ▸ e

@[simp]
theorem cast_rfl_rfl {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) : e.cast rfl rfl = e := rfl

@[simp]
theorem cast_cast
  {Γ Γ' Γ'' : Context} {τ τ' τ'' : Ty} (e : Γ ⊢ τ) (hΓ : Γ = Γ') (hΓ' : Γ' = Γ'') (hτ : τ = τ') (hτ' : τ' = τ'') :
  (e.cast hΓ hτ).cast hΓ' hτ' = e.cast (hΓ.trans hΓ') (hτ.trans hτ')
:= by
  subst_vars
  rfl

@[simp]
theorem cast_trans
  {Γ Γ' Γ'' : Context} {τ τ' τ'' : Ty} {e : Γ ⊢ τ} {e' : Γ' ⊢ τ'} {e'' : Γ'' ⊢ τ''}
  {hΓ : Γ = Γ'} {hΓ' : Γ' = Γ''} {hτ : τ = τ'} {hτ' : τ' = τ''}
  (he : e.cast hΓ hτ = e') (he' : e'.cast hΓ' hτ' = e'') :
  e.cast (hΓ.trans hΓ') (hτ.trans hτ') = e''
:= by
  subst_vars
  rfl

@[simp]
theorem cast_var
  {Γ Γ' : Context} {τ τ' : Ty}
  (a : Γ ∋ τ) (hΓ : Γ = Γ') (hτ : τ = τ') :
  (var a : Γ ⊢ τ).cast hΓ hτ = var (a.cast hΓ hτ)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_nullary_case
  {Γ Γ' : Context} {τ τ' : Ty}
  (e : Γ ⊢ Ty.void) (hΓ : Γ = Γ') (hτ : τ = τ') :
  (nullary_case e : Γ ⊢ τ).cast hΓ hτ = nullary_case (e.cast hΓ rfl)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_inl
  {Γ Γ' : Context} {τₗ τₗ' τᵣ τᵣ' : Ty}
  (e : Γ ⊢ τₗ) (hΓ : Γ = Γ') (hτₗ : τₗ = τₗ') (hτᵣ : τᵣ = τᵣ') :
  (inl e : Γ ⊢ Ty.sum τₗ τᵣ).cast hΓ (congr (hτₗ ▸ rfl) hτᵣ) = inl (e.cast hΓ hτₗ)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_inr
  {Γ Γ' : Context} {τₗ τₗ' τᵣ τᵣ' : Ty}
  (e : Γ ⊢ τᵣ) (hΓ : Γ = Γ') (hτₗ : τₗ = τₗ') (hτᵣ : τᵣ = τᵣ') :
  (inr e : Γ ⊢ Ty.sum τₗ τᵣ).cast hΓ (congr (hτₗ ▸ rfl) hτᵣ) = inr (e.cast hΓ hτᵣ)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_binary_case
  {Γ Γ' : Context} {τ τ' τₗ τₗ' τᵣ τᵣ' : Ty}
  (e : Γ ⊢ Ty.sum τₗ τᵣ) (eₗ : (τₗ :: Γ) ⊢ τ) (eᵣ : (τᵣ :: Γ) ⊢ τ)
  (hΓ : Γ = Γ') (hτ : τ = τ') (hτₗ : τₗ = τₗ') (hτᵣ : τᵣ = τᵣ') :
  (binary_case e eₗ eᵣ : Γ ⊢ τ).cast hΓ hτ = binary_case (e.cast hΓ (congr (hτₗ ▸ rfl) hτᵣ)) (eₗ.cast (congr (hτₗ ▸ rfl) hΓ) hτ) (eᵣ.cast (congr (hτᵣ ▸ rfl) hΓ) hτ)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_abstraction
  {Γ Γ' : Context} {τ₁ τ₂ τ₂' : Ty}
  (e : τ₁ :: Γ ⊢ τ₂) (hΓ : Γ = Γ') (hτ₂ : τ₂ = τ₂') :
  (abstraction e : Γ ⊢ Ty.arrow τ₁ τ₂).cast hΓ (hτ₂ ▸ rfl) = abstraction (e.cast (congr rfl hΓ) hτ₂)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_application
  {Γ Γ' : Context} {τ₁ τ₁' τ₂ τ₂' : Ty}
  (e₁ : Γ ⊢ Ty.arrow τ₁ τ₂) (e₂ : Γ ⊢ τ₁) (hΓ : Γ = Γ') (hτ₁ : τ₁ = τ₁') (hτ₂ : τ₂ = τ₂') :
  (application e₁ e₂ : Γ ⊢ τ₂).cast hΓ hτ₂ = application (e₁.cast hΓ (hτ₁ ▸ hτ₂ ▸ rfl)) (e₂.cast hΓ hτ₁)
:= by
  subst_vars
  rfl

def sizeOf_ge_1 {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) : sizeOf e ≥ 1 :=
by
  cases e <;> simp_arith

end Expr
