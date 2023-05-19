import Aesop

import Prod1.Statics

open Statics

namespace Dynamics

inductive Value {Γ : Context} : {τ : Ty} → (Γ ⊢ τ) → Type where
  | triv : Value (@Expr.triv Γ)
  
  | pair
      {τ₁ τ₂ : Ty} {e₁ : Γ ⊢ τ₁} {e₂ : Γ ⊢ τ₂} :
      Value e₁ →
      Value e₂ →
      Value (Expr.pair e₁ e₂)
  
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
theorem cast_triv
  {Γ Δ : Context} (hΓ : Γ = Δ) :
  (Value.triv : Value Expr.triv).cast hΓ rfl (Expr.cast_triv hΓ) = Value.triv :=
by
  subst_vars
  rfl

@[simp]
theorem cast_pair
  {Γ Δ : Context} {τ₁ τ₁' τ₂ τ₂' : Ty} {e₁ : Γ ⊢ τ₁} {e₂ : Γ ⊢ τ₂} (val₁ : Value e₁) (val₂ : Value e₂)
  (hΓ : Γ = Δ) (hτ₁ : τ₁ = τ₁') (hτ₂ : τ₂ = τ₂') :
  (Value.pair val₁ val₂ : Value (Expr.pair e₁ e₂)).cast hΓ (congr (hτ₁ ▸ rfl) hτ₂) (Expr.cast_pair e₁ e₂ hΓ hτ₁ hτ₂) = Value.pair (val₁.cast hΓ hτ₁ rfl) (val₂.cast hΓ hτ₂ rfl):=
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
  | .triv => Value.triv
  | .pair val₁ val₂ => Value.pair (val₁.rename ρ) (val₂.rename ρ)
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
  
  | pair₁
      {Γ : Context} {τ₁ τ₂ : Ty} {e₁ : Γ ⊢ τ₁} {e₂ : Γ ⊢ τ₂} :
      Neutral e₁ →
      Normal e₂ →
      Neutral (Expr.pair e₁ e₂)
  
  | pair₂
      {Γ : Context} {τ₁ τ₂ : Ty} {e₁ : Γ ⊢ τ₁} {e₂ : Γ ⊢ τ₂} :
      Value e₁ →
      Neutral e₂ →
      Neutral (Expr.pair e₁ e₂)
  
  | proj₁
      {Γ : Context} {τ₁ τ₂ : Ty} {e : Γ ⊢ Ty.prod τ₁ τ₂} :
      Neutral e →
      Neutral (Expr.proj₁ e)
  
  | proj₂
      {Γ : Context} {τ₁ τ₂ : Ty} {e : Γ ⊢ Ty.prod τ₁ τ₂} :
      Neutral e →
      Neutral (Expr.proj₂ e)

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
  | _, _, .pair₁ neut₁ norm₂ => by
      cases neut' with
      | pair₁ neut₁' norm₂' =>
          match Neutral.decEq neut₁ neut₁', Normal.decEq norm₂ norm₂' with
          | isTrue eq, isTrue eq' => subst_vars; exact isTrue rfl
          | isFalse ne, _ => exact isFalse (by simp_all only [Neutral.pair₁.injEq, false_and])
          | _, isFalse ne => exact isFalse (by simp_all only [Neutral.pair₁.injEq, and_false])
      | _ => exact isFalse (by simp only)
  | _, _, .pair₂ val₁ neut₂ => by 
      cases neut' with
      | pair₂ val₁' neut₂' =>
          match decEq val₁ val₁', Neutral.decEq neut₂ neut₂' with
          | isTrue eq, isTrue eq' => rw [eq, eq']; exact isTrue rfl
          | isFalse ne, _ => exact isFalse (by simp_all only [Neutral.pair₂.injEq, false_and])
          | _, isFalse ne => exact isFalse (by simp_all only [Neutral.pair₂.injEq, and_false])
      | _ => exact isFalse (by simp only)
  | _, _, .proj₁ neut => by
      cases neut' with
      | proj₁ neut' =>
          match Neutral.decEq neut neut' with
          | isTrue eq =>
              subst_vars
              exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Neutral.proj₁.injEq])
  | _, _, .proj₂ neut => by
      cases neut' with
      | proj₂ neut' =>
          match Neutral.decEq neut neut' with
          | isTrue eq =>
              subst_vars
              exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Neutral.proj₂.injEq])
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
theorem cast_pair₁
  {Γ Δ : Context} {τ₁ τ₁' τ₂ τ₂' : Ty} {e₁ : Γ ⊢ τ₁} {e₂ : Γ ⊢ τ₂} (neut₁ : Neutral e₁) (norm₂ : Normal e₂)
  (hΓ : Γ = Δ) (hτ₁ : τ₁ = τ₁') (hτ₂ : τ₂ = τ₂') :
  (Neutral.pair₁ neut₁ norm₂ : Neutral (Expr.pair e₁ e₂)).cast hΓ (hτ₂ ▸ hτ₁ ▸ rfl) (Expr.cast_pair e₁ e₂ hΓ hτ₁ hτ₂) = Neutral.pair₁ (neut₁.cast hΓ hτ₁ rfl) (norm₂.cast hΓ hτ₂ rfl) :=
by
  subst_vars
  rfl

@[simp]
theorem cast_pair₂
  {Γ Δ : Context} {τ₁ τ₁' τ₂ τ₂' : Ty} {e₁ : Γ ⊢ τ₁} {e₂ : Γ ⊢ τ₂} (val₁ : Value e₁) (neut₂ : Neutral e₂)
  (hΓ : Γ = Δ) (hτ₁ : τ₁ = τ₁') (hτ₂ : τ₂ = τ₂') :
  (Neutral.pair₂ val₁ neut₂ : Neutral (Expr.pair e₁ e₂)).cast hΓ (hτ₂ ▸ hτ₁ ▸ rfl) (Expr.cast_pair e₁ e₂ hΓ hτ₁ hτ₂) = Neutral.pair₂ (val₁.cast hΓ hτ₁ rfl) (neut₂.cast hΓ hτ₂ rfl) :=
by
  subst_vars
  rfl

@[simp]
theorem cast_proj₁
  {Γ Δ : Context} {τ₁ τ₁' τ₂ : Ty} {e : Γ ⊢ Ty.prod τ₁ τ₂} (neut : Neutral e) (hΓ : Γ = Δ) (hτ₁ : τ₁ = τ₁') :
  (Neutral.proj₁ neut : Neutral (Expr.proj₁ e)).cast hΓ hτ₁ (Expr.cast_proj₁ e hΓ hτ₁) = Neutral.proj₁ (neut.cast hΓ (congr (hτ₁ ▸ rfl) rfl) rfl) :=
by
  subst_vars
  rfl

@[simp]
theorem cast_proj₂
  {Γ Δ : Context} {τ₁ τ₂ τ₂' : Ty} {e : Γ ⊢ Ty.prod τ₁ τ₂} (neut : Neutral e) (hΓ : Γ = Δ) (hτ₂ : τ₂ = τ₂') :
  (Neutral.proj₂ neut : Neutral (Expr.proj₂ e)).cast hΓ hτ₂ (Expr.cast_proj₂ e hΓ hτ₂) = Neutral.proj₂ (neut.cast hΓ (hτ₂ ▸ rfl) rfl) :=
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
  | .pair₁ neut₁ norm₂ => Neutral.pair₁ (neut₁.rename ρ) (norm₂.rename ρ)
  | .pair₂ val₁ neut₂ => Neutral.pair₂ (val₁.rename ρ) (neut₂.rename ρ)
  | .proj₁ neut => Neutral.proj₁ (neut.rename ρ)
  | .proj₂ neut => Neutral.proj₂ (neut.rename ρ)
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
  | .triv, neut => nomatch neut
  | .pair val₁ _, .pair₁ neut₁ norm₂ => val₁.not_neutral neut₁
  | .pair _ val₂, .pair₂ val₁' neut₂ => val₂.not_neutral neut₂
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
  | .pair₁ neut₁ norm₂ => neut₁.not_closed
  | .pair₂ val₁ neut₂ => neut₂.not_closed
  | .proj₁ neut => neut.not_closed
  | .proj₂ neut => neut.not_closed
  | .application neut₁ norm₂ => neut₁.not_closed

theorem Value.irrelevant
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
  (val val' : Value e) →
  val = val'
  | .triv, .triv => rfl
  | .pair val₁ val₂, .pair val₁' val₂' => by rw [Value.irrelevant val₁ val₁', Value.irrelevant val₂ val₂']
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
  | .pair₁ neut₁ norm₂, .pair₁ neut₁' norm₂' => by rw [Neutral.irrelevant neut₁ neut₁', Normal.irrelevant norm₂ norm₂']
  | .pair₁ neut₁ norm₂, .pair₂ val₁' neut₂' => Empty.elim (val₁'.not_neutral neut₁)
  | .pair₂ val₁ neut₂, .pair₁ neut₁' norm₂' => Empty.elim (val₁.not_neutral neut₁')
  | .pair₂ val₁ neut₂, .pair₂ val₁' neut₂' => by rw [Value.irrelevant val₁ val₁', Neutral.irrelevant neut₂ neut₂']
  | .proj₁ neut, .proj₁ neut' => by rw [Neutral.irrelevant neut neut']
  | .proj₂ neut, .proj₂ neut' => by rw [Neutral.irrelevant neut neut']
  | .application neut₁ norm₂, .application neut₁' norm₂' => by rw [Neutral.irrelevant neut₁ neut₁', Normal.irrelevant norm₂ norm₂']

end
