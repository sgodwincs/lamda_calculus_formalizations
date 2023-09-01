import Aesop

import Stlc.Statics

open Statics

namespace Dynamics

inductive Value {Γ : Context} : {τ : Ty} → (Γ ⊢ τ) → Type where
  | number
      {num : Nat} :
      Value (@Typing.number Γ num)
  
  | string
      {s : String} :
      Value (@Typing.string Γ s)
  deriving DecidableEq, Repr

namespace Value

def strip_context
  {Γ : Context} {τ : Ty} {t : Γ ⊢ τ}
  (val : Value t) :
  Σ t : ⊢ τ, Value t :=
by
  cases val with
  | @number num => exact ⟨Typing.number num, Value.number⟩
  | @string s => exact ⟨Typing.string s, Value.string⟩

def renamed
  {Γ Δ : Context} {τ : Ty} {t : Γ ⊢ τ}
  (ρ : Rename Γ Δ) (val : Value t) :
  Value (Typing.rename ρ t) :=
by
  cases val with
  | number => simp only [Typing.rename]; exact Value.number
  | string => simp only [Typing.rename]; exact Value.string

end Value

mutual

  inductive Normal : {Γ : Context} → {τ : Ty} → (Γ ⊢ τ) → Type where
  | neutral
      {Γ : Context} {τ : Ty} {t : Γ ⊢ τ} :
      Neutral t →
      Normal t
  
  | value
      {Γ : Context} {τ : Ty} {t : Γ ⊢ τ} :
      Value t →
      Normal t
  deriving Repr

  inductive Neutral : {Γ : Context} → {τ : Ty} → (Γ ⊢ τ) → Type where
  | var
      {Γ : Context} {τ : Ty} (a : Γ ∋ τ) :
      Neutral (Typing.var a)
  
  | plus₁
      {Γ : Context} {t₁ t₂ : Γ ⊢ Ty.number} :
      Neutral t₁ →
      Normal t₂ →
      Neutral (Typing.plus t₁ t₂)
  
  | plus₂
      {Γ : Context} {t₁ t₂ : Γ ⊢ Ty.number} :
      Value t₁ →
      Neutral t₂ →
      Neutral (Typing.plus t₁ t₂)
  
  | times₁
      {Γ : Context} {t₁ t₂ : Γ ⊢ Ty.number} :
      Neutral t₁ →
      Normal t₂ →
      Neutral (Typing.times t₁ t₂)
  
  | times₂
      {Γ : Context} {t₁ t₂ : Γ ⊢ Ty.number} :
      Value t₁ →
      Neutral t₂ →
      Neutral (Typing.times t₁ t₂)
  
  | concatenate₁
      {Γ : Context} {t₁ t₂ : Γ ⊢ Ty.string} :
      Neutral t₁ →
      Normal t₂ →
      Neutral (Typing.concatenate t₁ t₂)
  
  | concatenate₂
      {Γ : Context} {t₁ t₂ : Γ ⊢ Ty.string} :
      Value t₁ →
      Neutral t₂ →
      Neutral (Typing.concatenate t₁ t₂)

  | length
      {Γ : Context} {t : Γ ⊢ Ty.string} :
      Neutral t →
      Neutral (Typing.length t)
  deriving Repr
  
end

mutual

private def normal_decEq {Γ : Context} {τ : Ty} {t : Γ ⊢ τ} (norm norm' : Normal t) : Decidable (norm = norm') :=
  match norm with
  | .value val => by
      cases norm' with
      | value val' =>
          match decEq val val' with
          | isTrue eq => rw [eq]; exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Normal.value.injEq])
      | _ => exact isFalse (by simp only)
  | .neutral neut => by
      cases norm' with
      | neutral neut' =>
          match neutral_decEq neut neut' with
          | isTrue eq => rw [eq]; exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Normal.neutral.injEq])
      | _ => exact isFalse (by simp only)

private def neutral_decEq {Γ : Context} {τ : Ty} {t : Γ ⊢ τ} (neut neut' : Neutral t) : Decidable (neut = neut') :=
by
  match τ, t, neut with
  | _, _, .var _ => cases neut'; exact isTrue rfl
  | _, _, .plus₁ neut₁ norm₂ =>
      cases neut' with
      | plus₁ neut₁' norm₂' =>
          match neutral_decEq neut₁ neut₁', normal_decEq norm₂ norm₂' with
          | isTrue eq, isTrue eq' => rw [eq, eq']; exact isTrue rfl
          | isFalse ne, _ => exact isFalse (by simp_all only [Neutral.plus₁.injEq, false_and])
          | _, isFalse ne => exact isFalse (by simp_all only [Neutral.plus₁.injEq, and_false])
      | _ => exact isFalse (by simp only)
  | _, _, .plus₂ val₁ neut₂ =>
      cases neut' with
      | plus₂ val₁' neut₂' =>
          match decEq val₁ val₁', neutral_decEq neut₂ neut₂' with
          | isTrue eq, isTrue eq' => rw [eq, eq']; exact isTrue rfl
          | isFalse ne, _ => exact isFalse (by simp_all only [Neutral.plus₂.injEq, false_and])
          | _, isFalse ne => exact isFalse (by simp_all only [Neutral.plus₂.injEq, and_false])
      | _ => exact isFalse (by simp only)
  | _, _, .times₁ neut₁ norm₂ =>
      cases neut' with
      | times₁ neut₁' norm₂' =>
          match neutral_decEq neut₁ neut₁', normal_decEq norm₂ norm₂' with
          | isTrue eq, isTrue eq' => rw [eq, eq']; exact isTrue rfl
          | isFalse ne, _ => exact isFalse (by simp_all only [Neutral.times₁.injEq, false_and])
          | _, isFalse ne => exact isFalse (by simp_all only [Neutral.times₁.injEq, and_false])
      | _ => exact isFalse (by simp only)
  | _, _, .times₂ val₁ neut₂ =>
      cases neut' with
      | times₂ val₁' neut₂' =>
          match decEq val₁ val₁', neutral_decEq neut₂ neut₂' with
          | isTrue eq, isTrue eq' => rw [eq, eq']; exact isTrue rfl
          | isFalse ne, _ => exact isFalse (by simp_all only [Neutral.times₂.injEq, false_and])
          | _, isFalse ne => exact isFalse (by simp_all only [Neutral.times₂.injEq, and_false])
      | _ => exact isFalse (by simp only)
  | _, _, .concatenate₁ neut₁ norm₂ =>
      cases neut' with
      | concatenate₁ neut₁' norm₂' =>
          match neutral_decEq neut₁ neut₁', normal_decEq norm₂ norm₂' with
          | isTrue eq, isTrue eq' => rw [eq, eq']; exact isTrue rfl
          | isFalse ne, _ => exact isFalse (by simp_all only [Neutral.concatenate₁.injEq, false_and])
          | _, isFalse ne => exact isFalse (by simp_all only [Neutral.concatenate₁.injEq, and_false])
      | _ => exact isFalse (by simp only)
  | _, _, .concatenate₂ val₁ neut₂ =>
      cases neut' with
      | concatenate₂ val₁' neut₂' =>
          match decEq val₁ val₁', neutral_decEq neut₂ neut₂' with
          | isTrue eq, isTrue eq' => rw [eq, eq']; exact isTrue rfl
          | isFalse ne, _ => exact isFalse (by simp_all only [Neutral.concatenate₂.injEq, false_and])
          | _, isFalse ne => exact isFalse (by simp_all only [Neutral.concatenate₂.injEq, and_false])
      | _ => exact isFalse (by simp only)
  | _, _, .length neut'' => 
      cases neut' with
      | length neut''' =>
          match neutral_decEq neut'' neut''' with
          | isTrue eq => rw [eq]; exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Neutral.length.injEq])

end

instance {Γ : Context} {τ : Ty} (t : Γ ⊢ τ) : DecidableEq (Normal t) := normal_decEq

instance {Γ : Context} {τ : Ty} (t : Γ ⊢ τ) : DecidableEq (Neutral t) := neutral_decEq

mutual

def Normal.renamed
  {Γ Δ : Context} {τ : Ty} {t : Γ ⊢ τ}
  (ρ : Rename Γ Δ) (norm : Normal t) :
  Normal (Typing.rename ρ t) :=
  match norm with
  | .neutral neut => by exact Normal.neutral (Neutral.renamed ρ neut)
  | .value val => by exact Normal.value (Value.renamed ρ val)

def Neutral.renamed
  {Γ Δ : Context} {τ : Ty} {t : Γ ⊢ τ}
  (ρ : Rename Γ Δ) (neut : Neutral t) :
  Neutral (Typing.rename ρ t) :=
by
  cases neut with
  | var a => simp only [Typing.rename]; exact Neutral.var (ρ a)
  | plus₁ neut₁ norm₂ =>
      simp only [Typing.rename]
      exact Neutral.plus₁ (Neutral.renamed ρ neut₁) (Normal.renamed ρ norm₂)
  | plus₂ val₁ neut₂ =>
      simp only [Typing.rename]
      exact Neutral.plus₂ (Value.renamed ρ val₁) (Neutral.renamed ρ neut₂)
  | times₁ neut₁ norm₂ =>
      simp only [Typing.rename]
      exact Neutral.times₁ (Neutral.renamed ρ neut₁) (Normal.renamed ρ norm₂)
  | times₂ val₁ neut₂ =>
      simp only [Typing.rename]
      exact Neutral.times₂ (Value.renamed ρ val₁) (Neutral.renamed ρ neut₂)
  | concatenate₁ neut₁ norm₂ =>
      simp only [Typing.rename]
      exact Neutral.concatenate₁ (Neutral.renamed ρ neut₁) (Normal.renamed ρ norm₂)
  | concatenate₂ val₁ neut₂ =>
      simp only [Typing.rename]
      exact Neutral.concatenate₂ (Value.renamed ρ val₁) (Neutral.renamed ρ neut₂)
  | length neut =>
      simp only [Typing.rename]
      exact Neutral.length (Neutral.renamed ρ neut)

end

def Value.normal
  {Γ : Context} {τ : Ty} {t : Γ ⊢ τ}
  (v : Value t) :
  Normal t := Normal.value v

def Value.not_neutral
  {Γ : Context} {τ : Ty} {t : Γ ⊢ τ} :
  Value t →
  Neutral t →
  Empty
  | .number, neut => nomatch neut
  | .string, neut => nomatch neut

def Neutral.normal
  {Γ : Context} {τ : Ty} {t : Γ ⊢ τ}
  (neut : Neutral t) :
  Normal t := Normal.neutral neut

def Neutral.not_a_value
  {Γ : Context} {τ : Ty} {t : Γ ⊢ τ}
  (neut : Neutral t)
  (v : Value t) :
  Empty := v.not_neutral neut

def Value.irrelevant
  {Γ : Context} {τ : Ty} {t : Γ ⊢ τ} :
  (val val' : Value t) →
  val = val'
  | .number, .number => rfl
  | .string, .string => rfl

mutual

  private theorem normal_irrelevant
    {Γ : Context} {τ : Ty} {t : Γ ⊢ τ} :
    (norm norm' : Normal t) →
    norm = norm'
    | .neutral neut, .neutral neut' => by rw [neutral_irrelevant neut neut']
    | .neutral neut, .value val' => Empty.elim (Value.not_neutral val' neut)
    | .value val, .value val' => by rw [Value.irrelevant val val']
    | .value val, .neutral neut' => Empty.elim (Value.not_neutral val neut')

  private theorem neutral_irrelevant
    {Γ : Context} {τ : Ty} {t : Γ ⊢ τ} :
    (neut neut' : Neutral t) →
    neut = neut'
    | .var _, .var _ => rfl
    | .plus₁ neut₁ norm₂, .plus₁ neut₁' norm₂' => by rw [neutral_irrelevant neut₁ neut₁', normal_irrelevant norm₂ norm₂']
    | .plus₁ neut₁ norm₂, .plus₂ v₁' neut₂' => Empty.elim (Value.not_neutral  v₁' neut₁)
    | .plus₂ v₁ neut₂, .plus₂ v₁' neut₂' => by rw [Value.irrelevant v₁ v₁', neutral_irrelevant neut₂ neut₂']
    | .plus₂ v₁ neut₂, .plus₁ neut₁' norm₂' => Empty.elim (Value.not_neutral v₁ neut₁')
    | .times₁ neut₁ norm₂, .times₁ neut₁' norm₂' => by rw [neutral_irrelevant neut₁ neut₁', normal_irrelevant norm₂ norm₂']
    | .times₁ neut₁ norm₂, .times₂ v₁' neut₂' => Empty.elim (Value.not_neutral v₁' neut₁)
    | .times₂ v₁ neut₂, .times₂ v₁' neut₂' => by rw [Value.irrelevant v₁ v₁', neutral_irrelevant neut₂ neut₂']
    | .times₂ v₁ neut₂, .times₁ neut₁' norm₂' => Empty.elim (Value.not_neutral v₁ neut₁')
    | .concatenate₁ neut₁ norm₂, .concatenate₁ neut₁' norm₂' => by rw [neutral_irrelevant neut₁ neut₁', normal_irrelevant norm₂ norm₂']
    | .concatenate₁ neut₁ norm₂, .concatenate₂ v₁' neut₂' => Empty.elim (Value.not_neutral v₁' neut₁)
    | .concatenate₂ v₁ neut₂, .concatenate₂ v₁' neut₂' => by rw [Value.irrelevant v₁ v₁', neutral_irrelevant neut₂ neut₂']
    | .concatenate₂ v₁ neut₂, .concatenate₁ neut₁' norm₂' => Empty.elim (Value.not_neutral v₁ neut₁')
    | .length neut, .length neut' => by rw [neutral_irrelevant neut neut']

end

theorem Normal.irrelevant
    {Γ : Context} {τ : Ty} {t : Γ ⊢ τ} :
  (norm norm' : Normal t) →
  norm = norm' := normal_irrelevant

theorem Neutral.irrelevant
    {Γ : Context} {τ : Ty} {t : Γ ⊢ τ} :
  (neut neut' : Neutral t) →
  neut = neut' := neutral_irrelevant
