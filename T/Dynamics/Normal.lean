import Aesop

import T.Statics

open Statics

namespace Dynamics

inductive Value {Γ : Context} : {τ : Ty} → (Γ ⊢ τ) → Type where
  | zero : Value (@Expr.zero Γ)
  
  | succ
      {e : Γ ⊢ Ty.nat} :
      Value e →
      Value (@Expr.succ Γ e)
  
  | abstraction
      {τ τ' : Ty} {e : τ :: Γ ⊢ τ'} :
      Value (Expr.abstraction e)
  deriving DecidableEq, Repr

namespace Value

def cast
  {Γ Δ : Context} {τ τ' : Ty} {e : Γ ⊢ τ} {e' : Δ ⊢ τ'}
  (val : Value e) (hΓ : Γ = Δ) (hτ : τ = τ') (he : e.cast hΓ hτ = e') : Value e' :=
by
  subst_vars
  simp only [Expr.cast_rfl_rfl] at val
  exact val

@[simp]
theorem cast_rfl_rfl {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} (val : Value e) : val.cast rfl rfl rfl = val := rfl

@[simp]
theorem cast_cast
  {Γ Δ Ψ : Context} {τ τ' τ'' : Ty} {e : Γ ⊢ τ} {e' : Δ ⊢ τ'} {e'' : Ψ ⊢ τ''}
  (val : Value e) (hΓ : Γ = Δ) (hΓ' : Δ = Ψ) (hτ : τ = τ') (hτ' : τ' = τ'') (he : e.cast hΓ hτ = e') (he' : e'.cast hΓ' hτ' = e'') :
  (val.cast hΓ hτ he).cast hΓ' hτ' he' = val.cast (hΓ.trans hΓ') (hτ.trans hτ') (Expr.cast_trans he he') :=
by
  subst_vars
  rfl

@[simp]
theorem cast_zero
  {Γ Δ : Context} (hΓ : Γ = Δ) :
  (Value.zero : Value Expr.zero).cast hΓ rfl (Expr.cast_zero hΓ) = Value.zero :=
by
  subst_vars
  rfl

@[simp]
theorem cast_succ
  {Γ Δ : Context} {e : Γ ⊢ Ty.nat} (val : Value e) (hΓ : Γ = Δ) :
  (Value.succ val : Value (Expr.succ e)).cast hΓ rfl (Expr.cast_succ e hΓ) = Value.succ (val.cast hΓ rfl rfl) :=
by
  subst_vars
  rfl

@[simp]
theorem cast_abstraction
  {Γ Δ : Context} {τ₁ τ₂ τ₂' : Ty} {e : τ₁ :: Γ ⊢ τ₂} (hΓ : Γ = Δ) (hτ : τ₂ = τ₂') :
  (Value.abstraction : Value (Expr.abstraction e)).cast hΓ (congr rfl hτ) (Expr.cast_abstraction e hΓ hτ) = Value.abstraction :=
by
  subst_vars
  rfl

def rename
  {Γ Δ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (ρ : Rename Γ Δ) :
  (val : Value e) →
  Value (Expr.rename ρ e)
  | .zero => Value.zero
  | .succ v => Value.succ (v.rename ρ)
  | .abstraction => Value.abstraction

end Value

mutual

  inductive Normal : {Γ : Context} → {τ : Ty} → (Γ ⊢ τ) → Type where
  | neutral
      {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
      Neutral e →
      Normal e
  
  | value
      {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
      Value e →
      Normal e
  deriving Repr

  inductive Neutral : {Γ : Context} → {τ : Ty} → (Γ ⊢ τ) → Type where
  | var
      {Γ : Context} {τ : Ty} (a : Γ ∋ τ) :
      Neutral (Expr.var a)
  
  | succ
      {Γ : Context} {e : Γ ⊢ Ty.nat} :
      Neutral e →
      Neutral (Expr.succ e)

  | recursor
      {Γ : Context} {τ : Ty} {e : Γ ⊢ Ty.nat} {e₀ : Γ ⊢ τ} {eₛ : τ :: Ty.nat :: Γ ⊢ τ} :
      Neutral e →
      Neutral (Expr.recursor e e₀ eₛ)

  | application
      {Γ : Context} {τ τ' : Ty} {e₁ : Γ ⊢ Ty.arrow τ τ'} {e₂ : Γ ⊢ τ} :
      Neutral e₁ →
      Normal e₂ →
      Neutral (Expr.application e₁ e₂)
  deriving Repr
  
end

mutual

def Normal.decEq {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} (norm norm' : Normal e) : Decidable (norm = norm') :=
  match norm, norm' with
  | .value val, .value val' =>
      match decEq val val' with
      | isTrue eq => by subst_vars; exact isTrue rfl
      | isFalse ne => isFalse (by simp_all only [Normal.value.injEq])
  | .value _, .neutral _ => isFalse (by simp only)
  | .neutral neut, .neutral neut' => by
      match Neutral.decEq neut neut' with
      | isTrue eq => rw [eq]; exact isTrue rfl
      | isFalse ne => exact isFalse (by simp_all only [Normal.neutral.injEq])
  | .neutral _, .value _ => isFalse (by simp only)

def Neutral.decEq {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} (neut neut' : Neutral e) : Decidable (neut = neut') :=
  match τ, e, neut with
  | _, _, .var _ => by cases neut'; exact isTrue rfl
  | _, _, .succ neut => by
      cases neut' with
      | succ neut' =>
          match Neutral.decEq neut neut' with
          | isTrue eq =>
              subst_vars
              exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Neutral.succ.injEq])
  | _, _, .recursor neut => by
      cases neut' with
      | recursor neut' =>
          match Neutral.decEq neut neut' with
          | isTrue eq => subst_vars; exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Neutral.recursor.injEq])
  | _, _, .application neut₁ norm₂ => by
      cases neut' with
      | application neut₁' norm₂' =>
          match Neutral.decEq neut₁ neut₁', Normal.decEq norm₂ norm₂' with
          | isTrue eq, isTrue eq' => subst_vars; exact isTrue rfl
          | isFalse ne, _ => exact isFalse (by simp_all only [Neutral.application.injEq, false_and])
          | _, isFalse ne => exact isFalse (by simp_all only [Neutral.application.injEq, and_false])

end

instance {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) : DecidableEq (Normal e) := Normal.decEq

instance {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) : DecidableEq (Neutral e) := Neutral.decEq

namespace Normal

def cast
  {Γ Δ : Context} {τ τ' : Ty} {e : Γ ⊢ τ} {e' : Δ ⊢ τ'}
  (norm : Normal e) (hΓ : Γ = Δ) (hτ : τ = τ') (he : e.cast hΓ hτ = e') : Normal e' :=
by
  subst_vars
  simp only [Expr.cast_rfl_rfl] at norm
  exact norm

@[simp]
theorem cast_rfl_rfl {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} (norm : Normal e) : norm.cast rfl rfl rfl = norm := rfl

@[simp]
theorem cast_cast
  {Γ Δ Ψ : Context} {τ τ' τ'' : Ty} {e : Γ ⊢ τ} {e' : Δ ⊢ τ'} {e'' : Ψ ⊢ τ''}
  (norm : Normal e) (hΓ : Γ = Δ) (hΓ' : Δ = Ψ) (hτ : τ = τ') (hτ' : τ' = τ'') (he : e.cast hΓ hτ = e') (he' : e'.cast hΓ' hτ' = e'') :
  (norm.cast hΓ hτ he).cast hΓ' hτ' he' = norm.cast (hΓ.trans hΓ') (hτ.trans hτ') (Expr.cast_trans he he') :=
by
  subst_vars
  rfl

end Normal

namespace Neutral

def cast
  {Γ Δ : Context} {τ τ' : Ty} {e : Γ ⊢ τ} {e' : Δ ⊢ τ'}
  (neut : Neutral e) (hΓ : Γ = Δ) (hτ : τ = τ') (he : e.cast hΓ hτ = e') : Neutral e' :=
by
  subst_vars
  simp only [Expr.cast_rfl_rfl] at neut
  exact neut

@[simp]
theorem cast_rfl_rfl {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} (neut : Neutral e) : neut.cast rfl rfl rfl = neut := rfl

@[simp]
theorem cast_cast
  {Γ Δ Ψ : Context} {τ τ' τ'' : Ty} {e : Γ ⊢ τ} {e' : Δ ⊢ τ'} {e'' : Ψ ⊢ τ''}
  (neut : Neutral e) (hΓ : Γ = Δ) (hΓ' : Δ = Ψ) (hτ : τ = τ') (hτ' : τ' = τ'') (he : e.cast hΓ hτ = e') (he' : e'.cast hΓ' hτ' = e'') :
  (neut.cast hΓ hτ he).cast hΓ' hτ' he' = neut.cast (hΓ.trans hΓ') (hτ.trans hτ') (Expr.cast_trans he he') :=
by
  subst_vars
  rfl

end Neutral

namespace Normal

@[simp]
theorem cast_value
  {Γ Δ : Context} {τ τ' : Ty} {e : Γ ⊢ τ} {e' : Δ ⊢ τ'}
  (val : Value e) (hΓ : Γ = Δ) (hτ : τ = τ') (he : e.cast hΓ hτ = e') :
  (Normal.value val : Normal e).cast hΓ hτ he = Normal.value (val.cast hΓ hτ he) :=
by
  subst_vars
  rfl

@[simp]
theorem cast_neutral
  {Γ Δ : Context} {τ τ' : Ty} {e : Γ ⊢ τ} {e' : Δ ⊢ τ'}
  (neut : Neutral e) (hΓ : Γ = Δ) (hτ : τ = τ') (he : e.cast hΓ hτ = e') :
  (Normal.neutral neut : Normal e).cast hΓ hτ he = Normal.neutral (neut.cast hΓ hτ he) :=
by
  subst_vars
  rfl

end Normal

namespace Neutral

@[simp]
theorem cast_var
  {Γ Δ : Context} {τ τ' : Ty} (a : Γ ∋ τ) (hΓ : Γ = Δ) (hτ : τ = τ'):
  (Neutral.var a : Neutral (Expr.var a)).cast hΓ hτ (Expr.cast_var a hΓ hτ) = Neutral.var (a.cast hΓ hτ) :=
by
  subst_vars
  rfl

@[simp]
theorem cast_succ
  {Γ Δ : Context} {e : Γ ⊢ Ty.nat} (neut : Neutral e) (hΓ : Γ = Δ) :
  (Neutral.succ neut : Neutral (Expr.succ e)).cast hΓ rfl (Expr.cast_succ e hΓ) = Neutral.succ (neut.cast hΓ rfl rfl) :=
by
  subst_vars
  rfl

@[simp]
theorem cast_recursor
  {Γ Δ : Context} {τ τ' : Ty} {e : Γ ⊢ Ty.nat} {e₀ : Γ ⊢ τ} {eₛ : τ :: Ty.nat :: Γ ⊢ τ} (neut : Neutral e) (hΓ : Γ = Δ) (hτ : τ = τ') :
  (Neutral.recursor neut : Neutral (Expr.recursor e e₀ eₛ)).cast hΓ hτ (Expr.cast_recursor e e₀ eₛ hΓ hτ) = Neutral.recursor (neut.cast hΓ rfl rfl) :=
by
  subst_vars
  rfl

@[simp]
theorem cast_application
  {Γ Δ : Context} {τ₁ τ₁' τ₂ τ₂' : Ty} {e₁ : Γ ⊢ Ty.arrow τ₁ τ₂} {e₂ : Γ ⊢ τ₁}
  (neut₁ : Neutral e₁) (norm₂ : Normal e₂) (hΓ : Γ = Δ) (hτ₁ : τ₁ = τ₁') (hτ₂ : τ₂ = τ₂') :
  (Neutral.application neut₁ norm₂ : Neutral (Expr.application e₁ e₂)).cast hΓ hτ₂ (Expr.cast_application e₁ e₂ hΓ hτ₁ hτ₂)
  = Neutral.application (neut₁.cast hΓ (congr (congr rfl hτ₁) hτ₂) rfl) (norm₂.cast hΓ hτ₁ rfl) :=
by
  subst_vars
  rfl

end Neutral

mutual

def Normal.rename
  {Γ Δ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (ρ : Rename Γ Δ) :
  (norm : Normal e) →
  Normal (Expr.rename ρ e)
  | .neutral neut => Normal.neutral (neut.rename ρ)
  | .value val => Normal.value (val.rename ρ)

def Neutral.rename
  {Γ Δ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (ρ : Rename Γ Δ) :
  (neut : Neutral e) →
  Neutral (Expr.rename ρ e)
  | .var a => Neutral.var (ρ a)
  | .succ neut => Neutral.succ (neut.rename ρ)
  | .recursor neut => Neutral.recursor (neut.rename ρ)
  | .application neut₁ norm₂ => Neutral.application (neut₁.rename ρ) (norm₂.rename ρ)

end

def Value.normal
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (val : Value e) :
  Normal e := Normal.value val

def Value.not_neutral
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
  Value e →
  Neutral e →
  Empty
  | .zero, neut => nomatch neut
  | .succ val, .succ neut => val.not_neutral neut
  | .abstraction, neut => nomatch neut

def Neutral.normal
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (neut : Neutral e) :
  Normal e := Normal.neutral neut

def Neutral.not_a_value
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (neut : Neutral e)
  (val : Value e) :
  Empty := val.not_neutral neut

def Neutral.not_closed
  {τ : Ty} {e : ⊢ τ}:
  Neutral e → Empty
  | .var a => nomatch a
  | .succ neut => neut.not_closed
  | .recursor neut => neut.not_closed
  | .application neut₁ norm₂ => neut₁.not_closed

def Normal.succ {Γ : Context} {e : Γ ⊢ Ty.nat} : Normal e → Normal (Expr.succ e)
  | .neutral neut => (Neutral.succ neut).normal
  | .value val => (Value.succ val).normal

theorem Value.irrelevant
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
  (val val' : Value e) →
  val = val'
  | .zero, .zero => rfl
  | .succ val, .succ val' => by rw [Value.irrelevant val val']
  | .abstraction, .abstraction => rfl

mutual

theorem Normal.irrelevant
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
  (norm norm' : Normal e) →
  norm = norm'
  | .neutral neut, .neutral neut' => by rw [Neutral.irrelevant neut neut']
  | .neutral neut, .value val' => Empty.elim (val'.not_neutral neut)
  | .value val, .value val' => by rw [Value.irrelevant val val']
  | .value val, .neutral neut' => Empty.elim (val.not_neutral neut')

theorem Neutral.irrelevant
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
  (neut neut' : Neutral e) →
  neut = neut'
  | .var _, .var _ => rfl
  | .succ neut, .succ neut' => by rw [Neutral.irrelevant neut neut']
  | .recursor neut, .recursor neut' => by rw [Neutral.irrelevant neut neut']
  | .application neut₁ norm₂, .application neut₁' norm₂' => by rw [Neutral.irrelevant neut₁ neut₁', Normal.irrelevant norm₂ norm₂']

end
