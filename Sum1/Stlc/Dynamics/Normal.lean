import Aesop

import Stlc.Statics

open Statics

namespace Dynamics

inductive Value {Γ : Context} : {τ : Ty} → (Γ ⊢ τ) → Type where
  | inl
      {τ : Ty} {e : Γ ⊢ τ} :
      Value e →
      Value (Expr.inl e)

  | inr
      {τ : Ty} {e : Γ ⊢ τ} :
      Value e →
      Value (Expr.inr e)

  | abstraction
      {τ τ' : Ty} {e : τ :: Γ ⊢ τ'} :
      Value (Expr.abstraction e)
  deriving DecidableEq, Repr

namespace Value

abbrev cast
  {Γ Γ' : Context} {τ τ' : Ty} {e : Γ ⊢ τ} {e' : Γ' ⊢ τ'}
  (val : Value e) (hΓ : Γ = Γ') (hτ : τ = τ') (he : e.cast hΓ hτ = e') : Value e' :=
by
  subst_vars
  exact val

@[simp]
theorem cast_rfl_rfl {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} (val : Value e) : val.cast rfl rfl rfl = val := rfl

@[simp]
theorem cast_cast
  {Γ Γ' Γ'' : Context} {τ τ' τ'' : Ty} {e : Γ ⊢ τ} {e' : Γ' ⊢ τ'} {e'' : Γ'' ⊢ τ''}
  (val : Value e) (hΓ : Γ = Γ') (hΓ' : Γ' = Γ'') (hτ : τ = τ') (hτ' : τ' = τ'') (he : e.cast hΓ hτ = e') (he' : e'.cast hΓ' hτ' = e'') :
  (val.cast hΓ hτ he).cast hΓ' hτ' he' = val.cast (hΓ.trans hΓ') (hτ.trans hτ') (Expr.cast_trans he he')
:= by
  subst_vars
  rfl

@[simp]
theorem cast_inl
  {Γ Γ' : Context} {τₗ τₗ' τᵣ τᵣ' : Ty} {e : Γ ⊢ τₗ}
  (val : Value e) (hΓ : Γ = Γ') (hτₗ : τₗ = τₗ') (hτᵣ : τᵣ = τᵣ') :
  (inl val : Value (Expr.inl e)).cast hΓ (congr (hτₗ ▸ rfl) hτᵣ) (Expr.cast_inl e hΓ hτₗ hτᵣ) = inl (val.cast hΓ hτₗ rfl)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_inr
  {Γ Γ' : Context} {τₗ τₗ' τᵣ τᵣ' : Ty} {e : Γ ⊢ τᵣ}
  (val : Value e) (hΓ : Γ = Γ') (hτₗ : τₗ = τₗ') (hτᵣ : τᵣ = τᵣ') :
  (inr val : Value (Expr.inr e)).cast hΓ (congr (hτₗ ▸ rfl) hτᵣ) (Expr.cast_inr e hΓ hτₗ hτᵣ) = inr (val.cast hΓ hτᵣ rfl)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_abstraction
  {Γ Γ' : Context} {τ₁ τ₂ τ₂' : Ty} {e : τ₁ :: Γ ⊢ τ₂} (hΓ : Γ = Γ') (hτ : τ₂ = τ₂') :
  (abstraction : Value (Expr.abstraction e)).cast hΓ (congr rfl hτ) (Expr.cast_abstraction e hΓ hτ) = abstraction :=
by
  subst_vars
  rfl

def rename
  {Γ Γ' : Context} {τ : Ty} {e : Γ ⊢ τ}
  (ρ : Rename Γ Γ') :
  (val : Value e) →
  Value (Expr.rename ρ e)
  | .inl val => Value.inl (val.rename ρ)
  | .inr val => Value.inr (val.rename ρ)
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

  | nullary_case
      {Γ : Context} {e : Γ ⊢ Ty.void} :
      Neutral e →
      Neutral (Expr.nullary_case e)

  | inl
      {Γ : Context} {τₗ τᵣ : Ty} {e : Γ ⊢ τₗ} :
      Neutral e →
      Neutral (@Expr.inl Γ τₗ τᵣ e)

  | inr
      {Γ : Context} {τₗ τᵣ : Ty} {e : Γ ⊢ τᵣ} :
      Neutral e →
      Neutral (@Expr.inr Γ τₗ τᵣ e)

  | binary_case
      {Γ : Context} {τ τₗ τᵣ : Ty} {e : Γ ⊢ Ty.sum τₗ τᵣ} {eₗ : (τₗ :: Γ) ⊢ τ} {eᵣ : (τᵣ :: Γ) ⊢ τ} :
      Neutral e →
      Neutral (Expr.binary_case e eₗ eᵣ)

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
  | _, _, .var _ => by
      cases neut' with
      | var => exact isTrue rfl
  | _, _, .nullary_case neut => by
      cases neut' with
      | nullary_case neut' =>
          match Neutral.decEq neut neut' with
          | isTrue eq => subst_vars; exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Neutral.nullary_case.injEq])
  | _, _, .inl neut => by
      cases neut' with
      | inl neut' =>
          match Neutral.decEq neut neut' with
          | isTrue eq => subst_vars; exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Neutral.inl.injEq])
  | _, _, .inr neut => by
      cases neut' with
      | inr neut' =>
          match Neutral.decEq neut neut' with
          | isTrue eq => subst_vars; exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Neutral.inr.injEq])
  | _, _, .binary_case neut => by
      cases neut' with
      | binary_case neut' =>
          match Neutral.decEq neut neut' with
          | isTrue eq => subst_vars; exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Neutral.binary_case.injEq])
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

abbrev cast
  {Γ Γ' : Context} {τ τ' : Ty} {e : Γ ⊢ τ} {e' : Γ' ⊢ τ'}
  (norm : Normal e) (hΓ : Γ = Γ') (hτ : τ = τ') (he : e.cast hΓ hτ = e') : Normal e' :=
by
  subst_vars
  exact norm

@[simp]
theorem cast_rfl_rfl {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} (norm : Normal e) : norm.cast rfl rfl rfl = norm := rfl

@[simp]
theorem cast_cast
  {Γ Γ' Γ'' : Context} {τ τ' τ'' : Ty} {e : Γ ⊢ τ} {e' : Γ' ⊢ τ'} {e'' : Γ'' ⊢ τ''}
  (norm : Normal e) (hΓ : Γ = Γ') (hΓ' : Γ' = Γ'') (hτ : τ = τ') (hτ' : τ' = τ'') (he : e.cast hΓ hτ = e') (he' : e'.cast hΓ' hτ' = e'') :
  (norm.cast hΓ hτ he).cast hΓ' hτ' he' = norm.cast (hΓ.trans hΓ') (hτ.trans hτ') (Expr.cast_trans he he')
:= by
  subst_vars
  rfl

end Normal

namespace Neutral

def cast
  {Γ Γ' : Context} {τ τ' : Ty} {e : Γ ⊢ τ} {e' : Γ' ⊢ τ'}
  (neut : Neutral e) (hΓ : Γ = Γ') (hτ : τ = τ') (he : e.cast hΓ hτ = e') : Neutral e'
:= by
  subst_vars
  exact neut

@[simp]
theorem cast_rfl_rfl {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} (neut : Neutral e) : neut.cast rfl rfl rfl = neut := rfl

@[simp]
theorem cast_cast
  {Γ Γ' Γ'' : Context} {τ τ' τ'' : Ty} {e : Γ ⊢ τ} {e' : Γ' ⊢ τ'} {e'' : Γ'' ⊢ τ''}
  (neut : Neutral e) (hΓ : Γ = Γ') (hΓ' : Γ' = Γ'') (hτ : τ = τ') (hτ' : τ' = τ'') (he : e.cast hΓ hτ = e') (he' : e'.cast hΓ' hτ' = e'') :
  (neut.cast hΓ hτ he).cast hΓ' hτ' he' = neut.cast (hΓ.trans hΓ') (hτ.trans hτ') (Expr.cast_trans he he')
:= by
  subst_vars
  rfl

end Neutral

namespace Normal

@[simp]
theorem cast_value
  {Γ Γ' : Context} {τ τ' : Ty} {e : Γ ⊢ τ} {e' : Γ' ⊢ τ'}
  (val : Value e) (hΓ : Γ = Γ') (hτ : τ = τ') (he : e.cast hΓ hτ = e') :
  (Normal.value val : Normal e).cast hΓ hτ he = Normal.value (val.cast hΓ hτ he)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_neutral
  {Γ Γ' : Context} {τ τ' : Ty} {e : Γ ⊢ τ} {e' : Γ' ⊢ τ'}
  (neut : Neutral e) (hΓ : Γ = Γ') (hτ : τ = τ') (he : e.cast hΓ hτ = e') :
  (Normal.neutral neut : Normal e).cast hΓ hτ he = Normal.neutral (neut.cast hΓ hτ he)
:= by
  subst_vars
  rfl

end Normal

namespace Neutral

@[simp]
theorem cast_var
  {Γ Γ' : Context} {τ τ' : Ty} (a : Γ ∋ τ) (hΓ : Γ = Γ') (hτ : τ = τ'):
  (Neutral.var a : Neutral (Expr.var a)).cast hΓ hτ (Expr.cast_var a hΓ hτ) = Neutral.var (a.cast hΓ hτ)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_nullary_case
  {Γ Γ' : Context} {τ τ' : Ty} {e : Γ ⊢ Ty.void}
  (neut : Neutral e) (hΓ : Γ = Γ') (hτ : τ = τ') :
  (Neutral.nullary_case neut : Neutral (Expr.nullary_case e)).cast hΓ hτ (Expr.cast_nullary_case e hΓ hτ) = nullary_case (neut.cast hΓ rfl rfl)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_inl
  {Γ Γ' : Context} {τₗ τₗ' τᵣ τᵣ' : Ty} {e : Γ ⊢ τₗ}
  (neut : Neutral e) (hΓ : Γ = Γ') (hτₗ : τₗ = τₗ') (hτᵣ : τᵣ = τᵣ') :
  (Neutral.inl neut : Neutral (Expr.inl e)).cast hΓ (congr (hτₗ ▸ rfl) hτᵣ) (Expr.cast_inl e hΓ hτₗ hτᵣ) = inl (neut.cast hΓ hτₗ rfl)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_inr
  {Γ Γ' : Context} {τₗ τₗ' τᵣ τᵣ' : Ty} {e : Γ ⊢ τᵣ}
  (neut : Neutral e) (hΓ : Γ = Γ') (hτₗ : τₗ = τₗ') (hτᵣ : τᵣ = τᵣ') :
  (Neutral.inr neut : Neutral (Expr.inr e)).cast hΓ (congr (hτₗ ▸ rfl) hτᵣ) (Expr.cast_inr e hΓ hτₗ hτᵣ) = inr (neut.cast hΓ hτᵣ rfl)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_binary_case
  {Γ Γ' : Context} {τ τ' τₗ τₗ' τᵣ τᵣ' : Ty} {e : Γ ⊢ Ty.sum τₗ τᵣ} {eₗ : (τₗ :: Γ) ⊢ τ} {eᵣ : (τᵣ :: Γ) ⊢ τ}
  (neut : Neutral e) (hΓ : Γ = Γ') (hτ : τ = τ') (hτₗ : τₗ = τₗ') (hτᵣ : τᵣ = τᵣ') :
  (Neutral.binary_case neut : Neutral (Expr.binary_case e eₗ eᵣ)).cast hΓ hτ (Expr.cast_binary_case e eₗ eᵣ hΓ hτ hτₗ hτᵣ)
  = binary_case (neut.cast hΓ (congr (hτₗ ▸ rfl) hτᵣ) rfl)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_application
  {Γ Γ' : Context} {τ₁ τ₁' τ₂ τ₂' : Ty} {e₁ : Γ ⊢ Ty.arrow τ₁ τ₂} {e₂ : Γ ⊢ τ₁}
  (neut₁ : Neutral e₁) (norm₂ : Normal e₂) (hΓ : Γ = Γ') (hτ₁ : τ₁ = τ₁') (hτ₂ : τ₂ = τ₂') :
  (Neutral.application neut₁ norm₂ : Neutral (Expr.application e₁ e₂)).cast hΓ hτ₂ (Expr.cast_application e₁ e₂ hΓ hτ₁ hτ₂)
  = Neutral.application (neut₁.cast hΓ (congr (congr rfl hτ₁) hτ₂) rfl) (norm₂.cast hΓ hτ₁ rfl)
:= by
  subst_vars
  rfl

end Neutral

mutual

def Normal.rename
  {Γ Γ' : Context} {τ : Ty} {e : Γ ⊢ τ}
  (ρ : Rename Γ Γ') :
  (norm : Normal e) →
  Normal (Expr.rename ρ e)
  | .neutral neut => Normal.neutral (neut.rename ρ)
  | .value val => Normal.value (val.rename ρ)

def Neutral.rename
  {Γ Γ' : Context} {τ : Ty} {e : Γ ⊢ τ}
  (ρ : Rename Γ Γ') :
  (neut : Neutral e) →
  Neutral (Expr.rename ρ e)
  | .var a => Neutral.var (ρ a)
  | .nullary_case neut => Neutral.nullary_case (neut.rename ρ)
  | .inl neut => Neutral.inl (neut.rename ρ)
  | .inr neut => Neutral.inr (neut.rename ρ)
  | .binary_case neut => Neutral.binary_case (neut.rename ρ)
  | .application neut₁ norm₂ => Neutral.application (neut₁.rename ρ) (norm₂.rename ρ)

end

@[aesop [safe forward, unsafe apply]]
abbrev Value.normal
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (val : Value e) :
  Normal e := Normal.value val

def Value.not_neutral
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
  Value e →
  Neutral e →
  Empty
  | .inl val, .inl neut => val.not_neutral neut
  | .inr val, .inr neut => val.not_neutral neut
  | .abstraction, neut => nomatch neut

@[aesop [safe forward, unsafe apply]]
abbrev Neutral.normal
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
  | .nullary_case neut => neut.not_closed
  | .inl neut => neut.not_closed
  | .inr neut => neut.not_closed
  | .binary_case neut => neut.not_closed
  | .application neut₁ norm₂ => neut₁.not_closed

def Normal.inl {Γ : Context} {τₗ τᵣ : Ty} {e : Γ ⊢ τₗ} : Normal e → Normal (@Expr.inl Γ τₗ τᵣ e)
  | .value val => (Value.inl val).normal
  | .neutral neut => (Neutral.inl neut).normal

def Normal.inr {Γ : Context} {τₗ τᵣ : Ty} {e : Γ ⊢ τᵣ} : Normal e → Normal (@Expr.inr Γ τₗ τᵣ e)
  | .value val => (Value.inr val).normal
  | .neutral neut => (Neutral.inr neut).normal

@[aesop safe [apply, forward]]
theorem Value.irrelevant
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
  (val val' : Value e) →
  val = val'
  | .inl val, .inl val' => by rw [Value.irrelevant val val']
  | .inr val, .inr val' => by rw [Value.irrelevant val val']
  | .abstraction, .abstraction => rfl

mutual

@[aesop safe [apply, forward]]
theorem Normal.irrelevant
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
  (norm norm' : Normal e) →
  norm = norm'
  | .neutral neut, .neutral neut' => by rw [Neutral.irrelevant neut neut']
  | .neutral neut, .value val' => Empty.elim (val'.not_neutral neut)
  | .value val, .value val' => by rw [Value.irrelevant val val']
  | .value val, .neutral neut' => Empty.elim (val.not_neutral neut')

@[aesop safe [apply, forward]]
theorem Neutral.irrelevant
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
  (neut neut' : Neutral e) →
  neut = neut'
  | .var _, .var _ => rfl
  | .nullary_case neut, .nullary_case neut' => by rw [Neutral.irrelevant neut neut']
  | .inl neut, .inl neut' => by rw [Neutral.irrelevant neut neut']
  | .inr neut, .inr neut' => by rw [Neutral.irrelevant neut neut']
  | .binary_case neut, .binary_case neut' => by rw [Neutral.irrelevant neut neut']
  | .application neut₁ norm₂, .application neut₁' norm₂' => by rw [Neutral.irrelevant neut₁ neut₁', Normal.irrelevant norm₂ norm₂']

end
