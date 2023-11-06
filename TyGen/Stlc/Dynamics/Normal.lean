import Aesop

import Stlc.Statics

open Statics

namespace Dynamics

inductive Value {Γ : Context} : {τ : Ty} → (Γ ⊢ τ) → Type where
  | triv : Value (@Expr.triv Γ)
  
  | pair
      {τₗ τᵣ : Ty} {eₗ : Γ ⊢ τₗ} {eᵣ : Γ ⊢ τᵣ} :
      Value eₗ →
      Value eᵣ →
      Value (Expr.pair eₗ eᵣ)

  | inₗ
      {τ : Ty} {eₗ : Γ ⊢ τ} :
      Value eₗ →
      Value (Expr.inₗ eₗ)
  
  | inᵣ
      {τ : Ty} {eᵣ : Γ ⊢ τ} :
      Value eᵣ →
      Value (Expr.inᵣ eᵣ)
  
  | abstraction
      {τ τ' : Ty} {e : τ :: Γ ⊢ τ'} :
      Value (Expr.abstraction e)
  deriving DecidableEq, Repr

namespace Value

abbrev cast
  {Γ Γ' : Context} {τ τ' : Ty} {e : Γ ⊢ τ} {e' : Γ' ⊢ τ'}
  (val : Value e) (hΓ : Γ = Γ') (hτ : τ = τ') (he : e.cast hΓ hτ = e') : Value e'
:= by
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
theorem cast_triv
  {Γ Γ' : Context} (hΓ : Γ = Γ') :
  (Value.triv : Value Expr.triv).cast hΓ rfl (Expr.cast_triv hΓ) = Value.triv :=
by
  subst_vars
  rfl

@[simp]
theorem cast_pair
  {Γ Γ' : Context} {τₗ τₗ' τᵣ τᵣ' : Ty} {eₗ : Γ ⊢ τₗ} {eᵣ : Γ ⊢ τᵣ} (valₗ : Value eₗ) (valᵣ : Value eᵣ)
  (hΓ : Γ = Γ') (hτₗ : τₗ = τₗ') (hτᵣ : τᵣ = τᵣ') :
  (Value.pair valₗ valᵣ : Value (Expr.pair eₗ eᵣ)).cast hΓ (congr (hτₗ ▸ rfl) hτᵣ) (Expr.cast_pair eₗ eᵣ hΓ hτₗ hτᵣ) = Value.pair (valₗ.cast hΓ hτₗ rfl) (valᵣ.cast hΓ hτᵣ rfl):=
by
  subst_vars
  rfl

@[simp]
theorem cast_inₗ
  {Γ Γ' : Context} {τₗ τₗ' τᵣ τᵣ' : Ty} {e : Γ ⊢ τₗ}
  (val : Value e) (hΓ : Γ = Γ') (hτₗ : τₗ = τₗ') (hτᵣ : τᵣ = τᵣ') :
  (inₗ val : Value (Expr.inₗ e)).cast hΓ (congr (hτₗ ▸ rfl) hτᵣ) (Expr.cast_inₗ e hΓ hτₗ hτᵣ) = inₗ (val.cast hΓ hτₗ rfl)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_inr
  {Γ Γ' : Context} {τₗ τₗ' τᵣ τᵣ' : Ty} {e : Γ ⊢ τᵣ}
  (val : Value e) (hΓ : Γ = Γ') (hτₗ : τₗ = τₗ') (hτᵣ : τᵣ = τᵣ') :
  (inᵣ val : Value (Expr.inᵣ e)).cast hΓ (congr (hτₗ ▸ rfl) hτᵣ) (Expr.cast_inᵣ e hΓ hτₗ hτᵣ) = inᵣ (val.cast hΓ hτᵣ rfl)
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
  | .triv => Value.triv
  | .pair valₗ valᵣ => Value.pair (valₗ.rename ρ) (valᵣ.rename ρ)
  | .inₗ val => Value.inₗ (val.rename ρ)
  | .inᵣ val => Value.inᵣ (val.rename ρ)
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
  
  | pairₗ
      {Γ : Context} {τₗ τᵣ : Ty} {eₗ : Γ ⊢ τₗ} {eᵣ : Γ ⊢ τᵣ} :
      Neutral eₗ →
      Normal eᵣ →
      Neutral (Expr.pair eₗ eᵣ)
  
  | pairᵣ
      {Γ : Context} {τₗ τᵣ : Ty} {eₗ : Γ ⊢ τₗ} {eᵣ : Γ ⊢ τᵣ} :
      Value eₗ →
      Neutral eᵣ →
      Neutral (Expr.pair eₗ eᵣ)
  
  | projₗ
      {Γ : Context} {τₗ τᵣ : Ty} {e : Γ ⊢ Ty.prod τₗ τᵣ} :
      Neutral e →
      Neutral (Expr.projₗ e)
  
  | projᵣ
      {Γ : Context} {τₗ τᵣ : Ty} {e : Γ ⊢ Ty.prod τₗ τᵣ} :
      Neutral e →
      Neutral (Expr.projᵣ e)
  
  | nullary_case
      {Γ : Context} {e : Γ ⊢ Ty.void} :
      Neutral e →
      Neutral (Expr.nullary_case e)
  
  | inₗ
      {Γ : Context} {τₗ τᵣ : Ty} {e : Γ ⊢ τₗ} :
      Neutral e →
      Neutral (@Expr.inₗ Γ τₗ τᵣ e)
  
  | inᵣ
      {Γ : Context} {τₗ τᵣ : Ty} {e : Γ ⊢ τᵣ} :
      Neutral e →
      Neutral (@Expr.inᵣ Γ τₗ τᵣ e)
  
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
  | _, _, .pairₗ neutₗ normᵣ => by
      cases neut' with
      | pairₗ neutₗ' normᵣ' =>
          match Neutral.decEq neutₗ neutₗ', Normal.decEq normᵣ normᵣ' with
          | isTrue eq, isTrue eq' => subst_vars; exact isTrue rfl
          | isFalse ne, _ => exact isFalse (by simp_all only [Neutral.pairₗ.injEq, false_and])
          | _, isFalse ne => exact isFalse (by simp_all only [Neutral.pairₗ.injEq, and_false])
      | _ => exact isFalse (by simp only)
  | _, _, .pairᵣ valₗ neutᵣ => by 
      cases neut' with
      | pairᵣ valₗ' neutᵣ' =>
          match decEq valₗ valₗ', Neutral.decEq neutᵣ neutᵣ' with
          | isTrue eq, isTrue eq' => rw [eq, eq']; exact isTrue rfl
          | isFalse ne, _ => exact isFalse (by simp_all only [Neutral.pairᵣ.injEq, false_and])
          | _, isFalse ne => exact isFalse (by simp_all only [Neutral.pairᵣ.injEq, and_false])
      | _ => exact isFalse (by simp only)
  | _, _, .projₗ neut => by
      cases neut' with
      | projₗ neut' =>
          match Neutral.decEq neut neut' with
          | isTrue eq =>
              subst_vars
              exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Neutral.projₗ.injEq])
  | _, _, .projᵣ neut => by
      cases neut' with
      | projᵣ neut' =>
          match Neutral.decEq neut neut' with
          | isTrue eq =>
              subst_vars
              exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Neutral.projᵣ.injEq])
  | _, _, .nullary_case neut => by
      cases neut' with
      | nullary_case neut' =>
          match Neutral.decEq neut neut' with
          | isTrue eq => subst_vars; exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Neutral.nullary_case.injEq])
  | _, _, .inₗ neutₗ => by
      cases neut' with
      | inₗ neutₗ' =>
          match Neutral.decEq neutₗ neutₗ' with
          | isTrue eq => subst_vars; exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Neutral.inₗ.injEq])
  | _, _, .inᵣ neutᵣ => by
      cases neut' with
      | inᵣ neutᵣ' =>
          match Neutral.decEq neutᵣ neutᵣ' with
          | isTrue eq => subst_vars; exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Neutral.inᵣ.injEq])
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
theorem cast_pairₗ
  {Γ Γ' : Context} {τₗ τₗ' τᵣ τᵣ' : Ty} {eₗ : Γ ⊢ τₗ} {eᵣ : Γ ⊢ τᵣ} (neutₗ : Neutral eₗ) (normᵣ : Normal eᵣ)
  (hΓ : Γ = Γ') (hτₗ : τₗ = τₗ') (hτᵣ : τᵣ = τᵣ') :
  (Neutral.pairₗ neutₗ normᵣ : Neutral (Expr.pair eₗ eᵣ)).cast hΓ (hτᵣ ▸ hτₗ ▸ rfl) (Expr.cast_pair eₗ eᵣ hΓ hτₗ hτᵣ) = Neutral.pairₗ (neutₗ.cast hΓ hτₗ rfl) (normᵣ.cast hΓ hτᵣ rfl)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_pairᵣ
  {Γ Γ' : Context} {τₗ τₗ' τᵣ τᵣ' : Ty} {eₗ : Γ ⊢ τₗ} {eᵣ : Γ ⊢ τᵣ} (valₗ : Value eₗ) (neutᵣ : Neutral eᵣ)
  (hΓ : Γ = Γ') (hτₗ : τₗ = τₗ') (hτᵣ : τᵣ = τᵣ') :
  (Neutral.pairᵣ valₗ neutᵣ : Neutral (Expr.pair eₗ eᵣ)).cast hΓ (hτᵣ ▸ hτₗ ▸ rfl) (Expr.cast_pair eₗ eᵣ hΓ hτₗ hτᵣ) = Neutral.pairᵣ (valₗ.cast hΓ hτₗ rfl) (neutᵣ.cast hΓ hτᵣ rfl)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_projₗ
  {Γ Γ' : Context} {τₗ τₗ' τᵣ : Ty} {e : Γ ⊢ Ty.prod τₗ τᵣ} (neut : Neutral e) (hΓ : Γ = Γ') (hτₗ : τₗ = τₗ') :
  (Neutral.projₗ neut : Neutral (Expr.projₗ e)).cast hΓ hτₗ (Expr.cast_projₗ e hΓ hτₗ) = Neutral.projₗ (neut.cast hΓ (congr (hτₗ ▸ rfl) rfl) rfl) :=
by
  subst_vars
  rfl

@[simp]
theorem cast_projᵣ
  {Γ Γ' : Context} {τₗ τᵣ τᵣ' : Ty} {e : Γ ⊢ Ty.prod τₗ τᵣ} (neut : Neutral e) (hΓ : Γ = Γ') (hτᵣ : τᵣ = τᵣ') :
  (Neutral.projᵣ neut : Neutral (Expr.projᵣ e)).cast hΓ hτᵣ (Expr.cast_projᵣ e hΓ hτᵣ) = Neutral.projᵣ (neut.cast hΓ (hτᵣ ▸ rfl) rfl) :=
by
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
theorem cast_inₗ
  {Γ Γ' : Context} {τₗ τₗ' τᵣ τᵣ' : Ty} {e : Γ ⊢ τₗ}
  (neut : Neutral e) (hΓ : Γ = Γ') (hτₗ : τₗ = τₗ') (hτᵣ : τᵣ = τᵣ') :
  (Neutral.inₗ neut : Neutral (Expr.inₗ e)).cast hΓ (congr (hτₗ ▸ rfl) hτᵣ) (Expr.cast_inₗ e hΓ hτₗ hτᵣ) = inₗ (neut.cast hΓ hτₗ rfl)
:= by
  subst_vars
  rfl

@[simp]
theorem cast_inᵣ
  {Γ Γ' : Context} {τₗ τₗ' τᵣ τᵣ' : Ty} {e : Γ ⊢ τᵣ}
  (neut : Neutral e) (hΓ : Γ = Γ') (hτₗ : τₗ = τₗ') (hτᵣ : τᵣ = τᵣ') :
  (Neutral.inᵣ neut : Neutral (Expr.inᵣ e)).cast hΓ (congr (hτₗ ▸ rfl) hτᵣ) (Expr.cast_inᵣ e hΓ hτₗ hτᵣ) = inᵣ (neut.cast hΓ hτᵣ rfl)
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
  | .pairₗ neutₗ normᵣ => Neutral.pairₗ (neutₗ.rename ρ) (normᵣ.rename ρ)
  | .pairᵣ valₗ neutᵣ => Neutral.pairᵣ (valₗ.rename ρ) (neutᵣ.rename ρ)
  | .projₗ neut => Neutral.projₗ (neut.rename ρ)
  | .projᵣ neut => Neutral.projᵣ (neut.rename ρ)
  | .nullary_case neut => Neutral.nullary_case (neut.rename ρ)
  | .inₗ neutₗ => Neutral.inₗ (neutₗ.rename ρ)
  | .inᵣ neutᵣ => Neutral.inᵣ (neutᵣ.rename ρ)
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
  | .triv, neut => nomatch neut
  | .pair valₗ _, .pairₗ neutₗ normᵣ => valₗ.not_neutral neutₗ
  | .pair _ valᵣ, .pairᵣ valₗ' neutᵣ => valᵣ.not_neutral neutᵣ
  | .inₗ valₗ, .inₗ neutₗ => valₗ.not_neutral neutₗ
  | .inᵣ valᵣ, .inᵣ neutᵣ => valᵣ.not_neutral neutᵣ
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
  | .pairₗ neutₗ normᵣ => neutₗ.not_closed
  | .pairᵣ valₗ neutᵣ => neutᵣ.not_closed
  | .projₗ neut => neut.not_closed
  | .projᵣ neut => neut.not_closed
  | .nullary_case neut => neut.not_closed
  | .inₗ neut => neut.not_closed
  | .inᵣ neut => neut.not_closed
  | .binary_case neut => neut.not_closed
  | .application neut₁ norm₂ => neut₁.not_closed

def Normal.inₗ {Γ : Context} {τₗ τᵣ : Ty} {eₗ : Γ ⊢ τₗ} : Normal eₗ → Normal (@Expr.inₗ Γ τₗ τᵣ eₗ)
  | .value val => (Value.inₗ val).normal
  | .neutral neut => (Neutral.inₗ neut).normal

def Normal.inᵣ {Γ : Context} {τₗ τᵣ : Ty} {eᵣ : Γ ⊢ τᵣ} : Normal eᵣ → Normal (@Expr.inᵣ Γ τₗ τᵣ eᵣ)
  | .value val => (Value.inᵣ val).normal
  | .neutral neut => (Neutral.inᵣ neut).normal

@[aesop safe [apply, forward]]
theorem Value.irrelevant
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
  (val val' : Value e) →
  val = val'
  | .triv, .triv => rfl
  | .pair valₗ valᵣ, .pair valₗ' valᵣ' => by rw [Value.irrelevant valₗ valₗ', Value.irrelevant valᵣ valᵣ']
  | .inₗ valₗ, .inₗ valₗ' => by rw [Value.irrelevant valₗ valₗ']
  | .inᵣ valᵣ, .inᵣ valᵣ' => by rw [Value.irrelevant valᵣ valᵣ']
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
  | .pairₗ neutₗ normᵣ, .pairₗ neutₗ' normᵣ' => by rw [Neutral.irrelevant neutₗ neutₗ', Normal.irrelevant normᵣ normᵣ']
  | .pairₗ neutₗ normᵣ, .pairᵣ valₗ' neutᵣ' => Empty.elim (valₗ'.not_neutral neutₗ)
  | .pairᵣ valₗ neutᵣ, .pairₗ neutₗ' normᵣ' => Empty.elim (valₗ.not_neutral neutₗ')
  | .pairᵣ valₗ neutᵣ, .pairᵣ valₗ' neutᵣ' => by rw [Value.irrelevant valₗ valₗ', Neutral.irrelevant neutᵣ neutᵣ']
  | .projₗ neut, .projₗ neut' => by rw [Neutral.irrelevant neut neut']
  | .projᵣ neut, .projᵣ neut' => by rw [Neutral.irrelevant neut neut']
  | .nullary_case neut, .nullary_case neut' => by rw [Neutral.irrelevant neut neut']
  | .inₗ neutₗ, .inₗ neutₗ' => by rw [Neutral.irrelevant neutₗ neutₗ']
  | .inᵣ neutᵣ, .inᵣ neutᵣ' => by rw [Neutral.irrelevant neutᵣ neutᵣ']
  | .binary_case neut, .binary_case neut' => by rw [Neutral.irrelevant neut neut']
  | .application neut₁ norm₂, .application neut₁' norm₂' => by rw [Neutral.irrelevant neut₁ neut₁', Normal.irrelevant norm₂ norm₂']

end
