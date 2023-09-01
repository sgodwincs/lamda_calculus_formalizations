import Aesop

import Stlc.Bound
import Stlc.Dynamics.Normal
import Stlc.Statics

open Statics

namespace Dynamics

inductive Transition {Γ : Context} : {τ : Ty} → (Γ ⊢ τ) → (Γ ⊢ τ) → Type where
  | ξ_plus₁
      {t₁ t₁' t₂ : Γ ⊢ Ty.number} :
      Transition t₁ t₁' →
      Transition (Typing.plus t₁ t₂) (Typing.plus t₁' t₂)

  | ξ_plus₂
      {t₁ t₂ t₂' : Γ ⊢ Ty.number} :
      Normal t₁ →
      Transition t₂ t₂' →
      Transition (Typing.plus t₁ t₂) (Typing.plus t₁ t₂')
  
  | β_plus
      {num₁ num₂ : Nat} :
      Normal (@Typing.number Γ num₁) →
      Normal (@Typing.number Γ num₂) →
      Transition (Typing.plus (@Typing.number Γ num₁) (@Typing.number Γ num₂)) (Typing.number (num₁ + num₂))
      
  | ξ_times₁
      {t₁ t₁' t₂ : Γ ⊢ Ty.number} :
      Transition t₁ t₁' →
      Transition (Typing.times t₁ t₂) (Typing.times t₁' t₂)

  | ξ_times₂
      {t₁ t₂ t₂' : Γ ⊢ Ty.number} :
      Normal t₁ →
      Transition t₂ t₂' →
      Transition (Typing.times t₁ t₂) (Typing.times t₁ t₂')
  
  | β_times
      {num₁ num₂ : Nat} :
      Normal (@Typing.number Γ num₁) →
      Normal (@Typing.number Γ num₂) →
      Transition (Typing.times (@Typing.number Γ num₁) (@Typing.number Γ num₂)) (Typing.number (num₁ * num₂))
      
  | ξ_concatenate₁
      {t₁ t₁' t₂ : Γ ⊢ Ty.string} :
      Transition t₁ t₁' →
      Transition (Typing.concatenate t₁ t₂) (Typing.concatenate t₁' t₂)

  | ξ_concatenate₂
      {t₁ t₂ t₂' : Γ ⊢ Ty.string} :
      Normal t₁ →
      Transition t₂ t₂' →
      Transition (Typing.concatenate t₁ t₂) (Typing.concatenate t₁ t₂')
  
  | β_concatenate
      {s₁ s₂ : String} :
      Normal (@Typing.string Γ s₁) →
      Normal (@Typing.string Γ s₂) →
      Transition (Typing.concatenate (@Typing.string Γ s₁) (@Typing.string Γ s₂)) (Typing.string (s₁ ++ s₂))

  | ξ_length
      {t t' : Γ ⊢ Ty.string} :
      Transition t t' →
      Transition (Typing.length t) (Typing.length t')
  
  | β_length
      {s : String} :
      Normal (@Typing.string Γ s) →
      Transition (Typing.length (@Typing.string Γ s)) (Typing.number s.length)

  | ξ_let
      {τ₁ τ₂ : Ty} {t₁ t₁' : Γ ⊢ τ₁} {t₂ : (τ₁ :: Γ) ⊢ τ₂} :
      Transition t₁ t₁' →
      Transition (Typing.let t₁ t₂) (Typing.let t₁' t₂)
  
  | β_let
      {τ₁ τ₂ : Ty} {t₁ : Γ ⊢ τ₁} {t₂ : (τ₁ :: Γ) ⊢ τ₂} {t' : Γ ⊢ τ₂} :
      t' = t₂ [ t₁ ] →
      Normal t₁ →
      Transition (Typing.let t₁ t₂) t'
  deriving DecidableEq

notation:40 t₁ " ⟶ " t₂ => Transition t₁ t₂

inductive Transitionᵣₜ {Γ : Context} : {τ : Ty} → (Γ ⊢ τ) → (Γ ⊢ τ) → Type where
  | refl
      {τ : Ty} :
      (t : Γ ⊢ τ) →
      Transitionᵣₜ t t
  
  | trans
      {τ : Ty}
      (t₁ : Γ ⊢ τ) {t₂ t₃ : Γ ⊢ τ} :
      (t₁ ⟶ t₂) →
      Transitionᵣₜ t₂ t₃ →
      Transitionᵣₜ t₁ t₃
  deriving DecidableEq

notation:20 t₁ " ⟶* " t₂ => Transitionᵣₜ t₁ t₂

namespace Transitionᵣₜ

def trans_tr_mtr
  {Γ : Context} {τ : Ty} {t₁ t₂ t₃ : Γ ⊢ τ}
  (tr : t₁ ⟶ t₂) (mtr' : t₂ ⟶* t₃) : (t₁ ⟶* t₃) := Transitionᵣₜ.trans _ tr mtr'

def trans_mtr_tr
  {Γ : Context} {τ : Ty} {t₁ t₂ t₃ : Γ ⊢ τ} :
  (t₁ ⟶* t₂) → (t₂ ⟶ t₃) → (t₁ ⟶* t₃)
  | .refl _, tr' => Transitionᵣₜ.trans _ tr' (Transitionᵣₜ.refl _)
  | .trans _ tr mtr, tr' => Transitionᵣₜ.trans _ tr (trans_mtr_tr mtr tr')

def trans'
  {Γ : Context} {τ : Ty} {t₁ t₂ t₃ : Γ ⊢ τ} :
  (t₁ ⟶* t₂) → (t₂ ⟶* t₃) → (t₁ ⟶* t₃)
  | .refl _, mtr' => mtr'
  | .trans _ tr mtr, mtr' => Transitionᵣₜ.trans _ tr (trans' mtr mtr')

end Transitionᵣₜ

def Transition.trans
  {Γ : Context} {τ : Ty} {t₁ t₂ t₃ : Γ ⊢ τ}
  (tr : t₁ ⟶ t₂) (tr' : t₂ ⟶ t₃) : (t₁ ⟶* t₃) :=
  match τ, t₁, t₂, tr with
  | .(_), .(_), .(_), .ξ_plus₁ tr₁ => Transitionᵣₜ.trans _ (Transition.ξ_plus₁ tr₁)
      (match tr' with
      | .ξ_plus₁ tr₁' => Transitionᵣₜ.trans _ (Transition.ξ_plus₁ tr₁') (Transitionᵣₜ.refl _)
      | .ξ_plus₂ norm₁' tr₂' => Transitionᵣₜ.trans _ (Transition.ξ_plus₂ norm₁' tr₂') (Transitionᵣₜ.refl _)
      | .β_plus norm₁' norm₂' => Transitionᵣₜ.trans _ (Transition.β_plus norm₁' norm₂') (Transitionᵣₜ.refl _))
  | .(_), .(_), .(_), .ξ_plus₂ norm₁ tr₂ => Transitionᵣₜ.trans _ (Transition.ξ_plus₂ norm₁ tr₂)
      (match tr' with
      | .ξ_plus₁ tr₁' => Transitionᵣₜ.trans _ (Transition.ξ_plus₁ tr₁') (Transitionᵣₜ.refl _)
      | .ξ_plus₂ norm₁' tr₂' => Transitionᵣₜ.trans _ (Transition.ξ_plus₂ norm₁' tr₂') (Transitionᵣₜ.refl _)
      | .β_plus norm₁' norm₂' => Transitionᵣₜ.trans _ (Transition.β_plus norm₁' norm₂') (Transitionᵣₜ.refl _))
  | .(_), .(_), .(_), .β_plus _ _ => nomatch tr'
  | .(_), .(_), .(_), .ξ_times₁ tr₁ => Transitionᵣₜ.trans _ (Transition.ξ_times₁ tr₁)
      (match tr' with
      | .ξ_times₁ tr₁' => Transitionᵣₜ.trans _ (Transition.ξ_times₁ tr₁') (Transitionᵣₜ.refl _)
      | .ξ_times₂ norm₁' tr₂' => Transitionᵣₜ.trans _ (Transition.ξ_times₂ norm₁' tr₂') (Transitionᵣₜ.refl _)
      | .β_times norm₁' norm₂' => Transitionᵣₜ.trans _ (Transition.β_times norm₁' norm₂') (Transitionᵣₜ.refl _))
  | .(_), .(_), .(_), .ξ_times₂ norm₁ tr₂ => Transitionᵣₜ.trans _ (Transition.ξ_times₂ norm₁ tr₂)
      (match tr' with
      | .ξ_times₁ tr₁' => Transitionᵣₜ.trans _ (Transition.ξ_times₁ tr₁') (Transitionᵣₜ.refl _)
      | .ξ_times₂ norm₁' tr₂' => Transitionᵣₜ.trans _ (Transition.ξ_times₂ norm₁' tr₂') (Transitionᵣₜ.refl _)
      | .β_times norm₁' norm₂' => Transitionᵣₜ.trans _ (Transition.β_times norm₁' norm₂') (Transitionᵣₜ.refl _))
  | .(_), .(_), .(_), .β_times _ _ => nomatch tr'
  | .(_), .(_), .(_), .ξ_concatenate₁ tr₁ => Transitionᵣₜ.trans _ (Transition.ξ_concatenate₁ tr₁)
      (match tr' with
      | .ξ_concatenate₁ tr₁' => Transitionᵣₜ.trans _ (Transition.ξ_concatenate₁ tr₁') (Transitionᵣₜ.refl _)
      | .ξ_concatenate₂ norm₁' tr₂' => Transitionᵣₜ.trans _ (Transition.ξ_concatenate₂ norm₁' tr₂') (Transitionᵣₜ.refl _)
      | .β_concatenate norm₁' norm₂' => Transitionᵣₜ.trans _ (Transition.β_concatenate norm₁' norm₂') (Transitionᵣₜ.refl _))
  | .(_), .(_), .(_), .ξ_concatenate₂ norm₁ tr₂ => Transitionᵣₜ.trans _ (Transition.ξ_concatenate₂ norm₁ tr₂)
      (match tr' with
      | .ξ_concatenate₁ tr₁' => Transitionᵣₜ.trans _ (Transition.ξ_concatenate₁ tr₁') (Transitionᵣₜ.refl _)
      | .ξ_concatenate₂ norm₁' tr₂' => Transitionᵣₜ.trans _ (Transition.ξ_concatenate₂ norm₁' tr₂') (Transitionᵣₜ.refl _)
      | .β_concatenate norm₁' norm₂' => Transitionᵣₜ.trans _ (Transition.β_concatenate norm₁' norm₂') (Transitionᵣₜ.refl _))
  | .(_), .(_), .(_), .β_concatenate _ _ => nomatch tr'
  | .(_), .(_), .(_), .ξ_length tr => Transitionᵣₜ.trans _ (Transition.ξ_length tr)
      (match tr' with
      | .ξ_length tr' => Transitionᵣₜ.trans _ (Transition.ξ_length tr') (Transitionᵣₜ.refl _)
      | .β_length norm' => Transitionᵣₜ.trans _ (Transition.β_length norm') (Transitionᵣₜ.refl _))
  | .(_), .(_), .(_), .β_length _ => nomatch tr'
  | .(_), .(_), .(_), .ξ_let tr₁ => Transitionᵣₜ.trans _ (Transition.ξ_let tr₁)
      (match tr' with
      | .ξ_let tr₁' => Transitionᵣₜ.trans _ (Transition.ξ_let tr₁') (Transitionᵣₜ.refl _)
      | .β_let h norm₁' => Transitionᵣₜ.trans _ (Transition.β_let h norm₁') (Transitionᵣₜ.refl _))
  | .(_), .(_), .(_), .β_let h norm₁ => Transitionᵣₜ.trans _ (Transition.β_let h norm₁) (Transitionᵣₜ.trans_tr_mtr tr' (Transitionᵣₜ.refl _))

instance {Γ : Context} {τ : Ty} : Trans (@Transition Γ τ) (@Transitionᵣₜ Γ τ) Transitionᵣₜ where
  trans := Transitionᵣₜ.trans_tr_mtr

instance {Γ : Context} {τ : Ty} : Trans (@Transitionᵣₜ Γ τ) (@Transition Γ τ) Transitionᵣₜ where
  trans := Transitionᵣₜ.trans_mtr_tr 

instance {Γ : Context} {τ : Ty} : Trans (@Transitionᵣₜ Γ τ) (@Transitionᵣₜ Γ τ) Transitionᵣₜ where
  trans := Transitionᵣₜ.trans'

instance {Γ : Context} {τ : Ty} : Trans (@Transition Γ τ) (@Transition Γ τ) Transitionᵣₜ where
  trans := Transition.trans

namespace Transitionᵣₜ

def ξ_plus₁
  {Γ : Context} {t₁ t₁' t₂ : Γ ⊢ Ty.number} :
  (t₁ ⟶* t₁') →
  (Typing.plus t₁ t₂ ⟶* Typing.plus t₁' t₂)
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr₁ mtr₁ =>
      calc
        _ ⟶ (Typing.plus _ _) := Transition.ξ_plus₁ tr₁
        _ ⟶* _ := ξ_plus₁ mtr₁

def ξ_plus₂
  {Γ : Context} {t₁ t₂ t₂' : Γ ⊢ Ty.number}
  (norm₁ : Normal t₁) :
  (t₂ ⟶* t₂') →
  (Typing.plus t₁ t₂ ⟶* Typing.plus t₁ t₂')
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr₂ mtr₂ =>
      calc
        _ ⟶ (Typing.plus _ _) := Transition.ξ_plus₂ norm₁ tr₂
        _ ⟶* _ := ξ_plus₂ norm₁ mtr₂

def ξ_times₁
  {Γ : Context} {t₁ t₁' t₂ : Γ ⊢ Ty.number} :
  (t₁ ⟶* t₁') →
  (Typing.times t₁ t₂ ⟶* Typing.times t₁' t₂)
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr₁ mtr₁ =>
      calc
        _ ⟶ (Typing.times _ _) := Transition.ξ_times₁ tr₁
        _ ⟶* _ := ξ_times₁ mtr₁

def ξ_times₂
  {Γ : Context} {t₁ t₂ t₂' : Γ ⊢ Ty.number}
  (norm₁ : Normal t₁) :
  (t₂ ⟶* t₂') →
  (Typing.times t₁ t₂ ⟶* Typing.times t₁ t₂')
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr₂ mtr₂ =>
      calc
        _ ⟶ (Typing.times _ _) := Transition.ξ_times₂ norm₁ tr₂
        _ ⟶* _ := ξ_times₂ norm₁ mtr₂

def ξ_concatenate₁
  {Γ : Context} {t₁ t₁' t₂ : Γ ⊢ Ty.string} :
  (t₁ ⟶* t₁') →
  (Typing.concatenate t₁ t₂ ⟶* Typing.concatenate t₁' t₂)
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr₁ mtr₁ =>
      calc
        _ ⟶ (Typing.concatenate _ _) := Transition.ξ_concatenate₁ tr₁
        _ ⟶* _ := ξ_concatenate₁ mtr₁

def ξ_concatenate₂
  {Γ : Context} {t₁ t₂ t₂' : Γ ⊢ Ty.string}
  (norm₁ : Normal t₁) :
  (t₂ ⟶* t₂') →
  (Typing.concatenate t₁ t₂ ⟶* Typing.concatenate t₁ t₂')
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr₂ mtr₂ =>
    calc
      _ ⟶ (Typing.concatenate _ _) := Transition.ξ_concatenate₂ norm₁ tr₂
      _ ⟶* _ := ξ_concatenate₂ norm₁ mtr₂

def ξ_length
  {Γ : Context} {t t' : Γ ⊢ Ty.string} :
  (t ⟶* t') →
  (Typing.length t ⟶* Typing.length t')
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr mtr =>
      calc
        _ ⟶ (Typing.length _) := Transition.ξ_length tr
        _ ⟶* _ := ξ_length mtr

def ξ_let
  {Γ : Context} {τ₁ τ₂ : Ty} {t₁ t₁' : Γ ⊢ τ₁} {t₂ : (τ₁ :: Γ) ⊢ τ₂} :
  (t₁ ⟶* t₁') →
  (Typing.let t₁ t₂ ⟶* Typing.let t₁' t₂)
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr₁ mtr₁ =>
      calc
        _ ⟶ (Typing.let _ _) := Transition.ξ_let tr₁
        _ ⟶* _ := ξ_let mtr₁

def length
  {Γ : Context} {τ : Ty} {t t' : Γ ⊢ τ} :
  (t ⟶* t') →
  Nat
  | .refl _ => 0
  | .trans _ _ mtr => 1 + length mtr

end Transitionᵣₜ

def _root_.Statics.Typing.normal_or_reduces
  {Γ : Context} {τ : Ty} :
  (t : Γ ⊢ τ) → 
  Sum (Normal t) (Σ t' : Γ ⊢ τ, t ⟶ t')
  | .var i => Sum.inl (Neutral.var i).normal
  | .number _ => Sum.inl Value.number.normal
  | .string _ => Sum.inl Value.string.normal
  | .plus t₁ t₂ =>
      match t₁.normal_or_reduces, t₂.normal_or_reduces with
      | .inl (.value .number), .inl (.value .number) => Sum.inr ⟨_, Transition.β_plus Value.number.normal Value.number.normal⟩
      | .inl (.value .number), .inl (.neutral neut₂) => Sum.inl (Neutral.plus₂ Value.number neut₂).normal
      | .inl (.value .number), .inr ⟨_, tr₂⟩ => Sum.inr ⟨_, Transition.ξ_plus₂ Value.number.normal tr₂⟩
      | .inl (.neutral neut₁), .inl norm₂ => Sum.inl (Neutral.plus₁ neut₁ norm₂).normal
      | .inl (.neutral neut₁), .inr ⟨_, tr₂⟩ => Sum.inr ⟨_, Transition.ξ_plus₂ neut₁.normal tr₂⟩
      | .inr ⟨_, tr₁⟩, _ => Sum.inr ⟨_, Transition.ξ_plus₁ tr₁⟩
  | .times t₁ t₂ =>
      match t₁.normal_or_reduces, t₂.normal_or_reduces with
      | .inl (.value .number), .inl (.value .number) => Sum.inr ⟨_, Transition.β_times Value.number.normal Value.number.normal⟩
      | .inl (.value .number), .inl (.neutral neut₂) => Sum.inl (Neutral.times₂ Value.number neut₂).normal
      | .inl (.value .number), .inr ⟨_, tr₂⟩ => Sum.inr ⟨_, Transition.ξ_times₂ Value.number.normal tr₂⟩
      | .inl (.neutral neut₁), .inl norm₂ => Sum.inl (Neutral.times₁ neut₁ norm₂).normal
      | .inl (.neutral neut₁), .inr ⟨_, tr₂⟩ => Sum.inr ⟨_, Transition.ξ_times₂ neut₁.normal tr₂⟩
      | .inr ⟨_, tr₁⟩, _ => Sum.inr ⟨_, Transition.ξ_times₁ tr₁⟩
  | .concatenate t₁ t₂ =>
      match t₁.normal_or_reduces, t₂.normal_or_reduces with
      | .inl (.value .string), .inl (.value .string) => Sum.inr ⟨_, Transition.β_concatenate Value.string.normal Value.string.normal⟩
      | .inl (.value .string), .inl (.neutral neut₂) => Sum.inl (Neutral.concatenate₂ Value.string neut₂).normal
      | .inl (.value .string), .inr ⟨_, tr₂⟩ => Sum.inr ⟨_, Transition.ξ_concatenate₂ Value.string.normal tr₂⟩
      | .inl (.neutral neut₁), .inl norm₂ => Sum.inl (Neutral.concatenate₁ neut₁ norm₂).normal
      | .inl (.neutral neut₁), .inr ⟨_, tr₂⟩ => Sum.inr ⟨_, Transition.ξ_concatenate₂ neut₁.normal tr₂⟩
      | .inr ⟨_, tr₁⟩, _ => Sum.inr ⟨_, Transition.ξ_concatenate₁ tr₁⟩
  | .length t =>
      match t.normal_or_reduces with
      | .inl (.value .string) => Sum.inr ⟨_, Transition.β_length Value.string.normal⟩
      | .inl (.neutral neut) => Sum.inl (Neutral.length neut).normal
      | .inr ⟨_, tr⟩ => Sum.inr ⟨_, Transition.ξ_length tr⟩
  | .let t₁ t₂ =>
      match t₁.normal_or_reduces with
      | .inl norm₁ => Sum.inr ⟨_, Transition.β_let rfl norm₁⟩
      | .inr ⟨_, tr₁⟩ => Sum.inr ⟨_, Transition.ξ_let tr₁⟩

def _root_.Statics.Typing.normal_if_no_reduction
  {Γ : Context} {τ : Ty} {t₁ : Γ ⊢ τ}
  (not_tr : {t₂ : Γ ⊢ τ} → (t₁ ⟶ t₂) → Empty) :
  Normal t₁ :=
  match t₁ with
  | .var i => (Neutral.var i).normal
  | .number _ => Value.number.normal
  | .string _ => Value.string.normal
  | .plus t₁ e₂ =>
      match t₁.normal_or_reduces, e₂.normal_or_reduces with
      | .inl (.value .number), .inl (.value .number) => Empty.elim (not_tr (Transition.β_plus Value.number.normal Value.number.normal))
      | .inl (.value .number), .inl (.neutral neut₂) => (Neutral.plus₂ Value.number neut₂).normal
      | .inl (.neutral neut₁), .inl norm₂ => (Neutral.plus₁ neut₁ norm₂).normal
      | .inl norm₁, .inr ⟨_, tr₂⟩ => Empty.elim (not_tr (Transition.ξ_plus₂ norm₁ tr₂))
      | .inr ⟨_, tr₁⟩, _ => Empty.elim (not_tr (Transition.ξ_plus₁ tr₁))
  | .times t₁ e₂ =>
      match t₁.normal_or_reduces, e₂.normal_or_reduces with
      | .inl (.value .number), .inl (.value .number) => Empty.elim (not_tr (Transition.β_times Value.number.normal Value.number.normal))
      | .inl (.value .number), .inl (.neutral neut₂) => (Neutral.times₂ Value.number neut₂).normal
      | .inl (.neutral neut₁), .inl norm₂ => (Neutral.times₁ neut₁ norm₂).normal
      | .inl norm₁, .inr ⟨_, tr₂⟩ => Empty.elim (not_tr (Transition.ξ_times₂ norm₁ tr₂))
      | .inr ⟨_, tr₁⟩, _ => Empty.elim (not_tr (Transition.ξ_times₁ tr₁))
  | .concatenate t₁ e₂ =>
      match t₁.normal_or_reduces, e₂.normal_or_reduces with
      | .inl (.value .string), .inl (.neutral neut₂) => (Neutral.concatenate₂ Value.string neut₂).normal
      | .inl (.value .string), .inl (.value .string) => Empty.elim (not_tr (Transition.β_concatenate Value.string.normal Value.string.normal))
      | .inl (.neutral neut₁), .inl norm₂ => (Neutral.concatenate₁ neut₁ norm₂).normal
      | .inl norm₁, .inr ⟨_, tr₂⟩ => Empty.elim (not_tr (Transition.ξ_concatenate₂ norm₁ tr₂))
      | .inr ⟨_, tr₁⟩, _ => Empty.elim (not_tr (Transition.ξ_concatenate₁ tr₁))
  | .length e =>
      match e.normal_or_reduces with
      | .inl (.value .string) => Empty.elim (not_tr (Transition.β_length Value.string.normal))
      | .inl (.neutral neut) => (Neutral.length neut).normal
      | .inr ⟨_, tr⟩ => Empty.elim (not_tr (Transition.ξ_length tr))
  | .let t₁ e₂ =>
      match t₁.normal_or_reduces with
      | .inl norm₁ => Empty.elim (not_tr (Transition.β_let rfl norm₁))
      | .inr ⟨_, tr₁⟩ => Empty.elim (not_tr (Transition.ξ_let tr₁))

def Value.does_not_reduce
  {Γ : Context} {τ : Ty} {t₁ t₂ : Γ ⊢ τ} :
  Value t₁ →
  (t₁ ⟶ t₂) →
  Empty
  | .number, tr => nomatch tr
  | .string, tr => nomatch tr

private theorem normal_or_neutral_does_not_reduce
  {Γ : Context} {τ : Ty} {t₁ t₂ : Γ ⊢ τ}
  (norm_or_neut : Sum (Normal t₁) (Neutral t₁))
  (tr : t₁ ⟶ t₂) :
  Empty :=
  match t₁, norm_or_neut, tr with
  | _, .inl (.neutral neut), tr => normal_or_neutral_does_not_reduce (Sum.inr neut) tr
  | .number _, .inl (.value .number), tr => nomatch tr
  | .string _, .inl (.value .string), tr => nomatch tr
  | .plus _ _, .inr (.plus₁ neut₁ _), .ξ_plus₁ tr₁ => normal_or_neutral_does_not_reduce (Sum.inr neut₁) tr₁
  | .plus _ _, .inr (.plus₁ _ norm₂), .ξ_plus₂ norm₁ tr₂ => normal_or_neutral_does_not_reduce (Sum.inl norm₂) tr₂
  | .plus _ _, .inr (.plus₂ v₁ _), .ξ_plus₁ tr₁ => v₁.does_not_reduce tr₁
  | .plus _ _, .inr (.plus₂ _ neut₂), .ξ_plus₂ norm₁ tr₂ => normal_or_neutral_does_not_reduce (Sum.inr neut₂) tr₂
  | .times _ _, .inr (.times₁ neut₁ _), .ξ_times₁ tr₁ => normal_or_neutral_does_not_reduce (Sum.inr neut₁) tr₁
  | .times _ _, .inr (.times₁ _ norm₂), .ξ_times₂ norm₁ tr₂ => normal_or_neutral_does_not_reduce (Sum.inl norm₂) tr₂
  | .times _ _, .inr (.times₂ v₁ _), .ξ_times₁ tr₁ => v₁.does_not_reduce tr₁
  | .times _ _, .inr (.times₂ _ neut₂), .ξ_times₂ norm₁ tr₂ => normal_or_neutral_does_not_reduce (Sum.inr neut₂) tr₂
  | .concatenate _ _, .inr (.concatenate₁ neut₁ _), .ξ_concatenate₁ tr₁ => normal_or_neutral_does_not_reduce (Sum.inr neut₁) tr₁
  | .concatenate _ _, .inr (.concatenate₁ _ norm₂), .ξ_concatenate₂ norm₁ tr₂ => normal_or_neutral_does_not_reduce (Sum.inl norm₂) tr₂
  | .concatenate _ _, .inr (.concatenate₂ v₁ _), .ξ_concatenate₁ tr₁ => v₁.does_not_reduce tr₁
  | .concatenate _ _, .inr (.concatenate₂ _ neut₂), .ξ_concatenate₂ norm₁ tr₂ => normal_or_neutral_does_not_reduce (Sum.inr neut₂) tr₂
  | .length _, .inr (.length neut), .ξ_length tr => normal_or_neutral_does_not_reduce (Sum.inr neut) tr

theorem Normal.does_not_reduce
  {Γ : Context} {τ : Ty} {t₁ t₂ : Γ ⊢ τ}
  (norm : Normal t₁)
  (tr : t₁ ⟶ t₂) :
  Empty := normal_or_neutral_does_not_reduce (Sum.inl norm) tr

theorem Neutral.does_not_reduce
  {Γ : Context} {τ : Ty} {t₁ t₂ : Γ ⊢ τ}
  (neut : Neutral t₁)
  (tr : t₁ ⟶ t₂) :
  Empty := normal_or_neutral_does_not_reduce (Sum.inr neut) tr

namespace Transition

theorem irrelevant
  {Γ : Context} {τ : Ty} {t t' : Γ ⊢ τ}
  (tr tr' : t ⟶ t') : 
  tr = tr' :=
by
  induction tr with
  | ξ_plus₁ tr ih =>
      cases tr' with
      | ξ_plus₁ tr' => rw [ih tr']
      | ξ_plus₂ norm₁' tr' => exact Empty.elim (norm₁'.does_not_reduce tr)
  | ξ_plus₂ norm₁ tr ih =>
      cases tr' with
      | ξ_plus₁ tr' => exact Empty.elim (norm₁.does_not_reduce tr')
      | ξ_plus₂ norm₁' tr' => rw [ih tr', Normal.irrelevant norm₁ norm₁']
  | β_plus norm₁ norm₂ =>
      cases tr' with
      | β_plus norm₁' norm₂' => rw [Normal.irrelevant norm₁ norm₁', Normal.irrelevant norm₂ norm₂']
  | ξ_times₁ tr ih =>
      cases tr' with
      | ξ_times₁ tr' => rw [ih tr']
      | ξ_times₂ norm₁' tr' => exact Empty.elim (norm₁'.does_not_reduce tr)
  | ξ_times₂ norm₁ tr ih =>
      cases tr' with
      | ξ_times₁ tr' => exact Empty.elim (norm₁.does_not_reduce tr')
      | ξ_times₂ norm₁' tr' => rw [ih tr', Normal.irrelevant norm₁ norm₁']
  | β_times norm₁ norm₂ =>
      cases tr' with
      | β_times norm₁' norm₂' => rw [Normal.irrelevant norm₁ norm₁', Normal.irrelevant norm₂ norm₂']
  | ξ_concatenate₁ tr ih =>
      cases tr' with
      | ξ_concatenate₁ tr' => rw [ih tr']
      | ξ_concatenate₂ norm₁' tr' => exact Empty.elim (norm₁'.does_not_reduce tr)
  | ξ_concatenate₂ norm₁ tr ih =>
      cases tr' with
      | ξ_concatenate₁ tr' => exact Empty.elim (norm₁.does_not_reduce tr')
      | ξ_concatenate₂ norm₁' tr' => rw [ih tr', Normal.irrelevant norm₁ norm₁']
  | β_concatenate norm₁ norm₂ =>
      cases tr' with
      | β_concatenate norm₁' norm₂' => rw [Normal.irrelevant norm₁ norm₁', Normal.irrelevant norm₂ norm₂']
  | ξ_length tr ih =>
      cases tr' with
      | ξ_length tr' => rw [ih tr']
  | β_length norm =>
      cases tr' with
      | β_length norm' => rw [Normal.irrelevant norm norm']
  | ξ_let tr ih =>
      cases tr' with
      | ξ_let tr' => rw [ih tr']
      | β_let h norm' => exact Empty.elim (Normal.does_not_reduce norm' tr)
  | β_let h norm =>
      cases tr' with
      | ξ_let tr' => exact Empty.elim (Normal.does_not_reduce norm tr')
      | β_let h' norm' => rw [Normal.irrelevant norm norm']

theorem deterministic
  {Γ : Context} {τ : Ty} {t₁ t₂ t₂' : Γ ⊢ τ}
  (tr : t₁ ⟶ t₂)
  (tr' : t₁ ⟶ t₂') : 
  t₂ = t₂' :=
by
  induction tr with
  | ξ_plus₁ tr ih => 
      cases tr' with
      | ξ_plus₁ tr' => rw [ih tr']
      | ξ_plus₂ norm₁' tr' => exact Empty.elim (norm₁'.does_not_reduce tr)
      | β_plus norm₁' norm₂' => exact Empty.elim (norm₁'.does_not_reduce tr)
  | ξ_plus₂ norm₁ tr ih => 
      cases tr' with
      | ξ_plus₂ norm₁' tr' => rw [ih tr']
      | ξ_plus₁ tr' => exact Empty.elim (norm₁.does_not_reduce tr')
      | β_plus norm₁' norm₂' => exact Empty.elim (norm₂'.does_not_reduce tr)
  | β_plus norm₁ norm₂ =>
      cases tr' with
      | β_plus norm₁' norm₂' => rfl
      | ξ_plus₁ tr' => exact Empty.elim (norm₁.does_not_reduce tr')
      | ξ_plus₂ norm₁' tr' => exact Empty.elim (norm₂.does_not_reduce tr')
  | ξ_times₁ tr ih =>
      cases tr' with
      | ξ_times₁ tr' => rw [ih tr']
      | ξ_times₂ norm₁' tr' => exact Empty.elim (norm₁'.does_not_reduce tr)
      | β_times norm₁' norm₂' => exact Empty.elim (norm₁'.does_not_reduce tr)
  | ξ_times₂ norm₁ tr ih => 
      cases tr' with
      | ξ_times₂ norm₁' tr' => rw [ih tr']
      | ξ_times₁ tr' => exact Empty.elim (norm₁.does_not_reduce tr')
      | β_times norm₁' norm₂' => exact Empty.elim (norm₂'.does_not_reduce tr)
  | β_times norm₁ norm₂ =>
      cases tr' with
      | β_times norm₁' norm₂' => rfl
      | ξ_times₁ tr' => exact Empty.elim (norm₁.does_not_reduce tr')
      | ξ_times₂ norm₁' tr' => exact Empty.elim (norm₂.does_not_reduce tr')
  | ξ_concatenate₁ tr ih => 
      cases tr' with
      | ξ_concatenate₁ tr' => rw [ih tr']
      | ξ_concatenate₂ norm₁' tr' => exact Empty.elim (norm₁'.does_not_reduce tr)
      | β_concatenate norm₁' norm₂' => exact Empty.elim (norm₁'.does_not_reduce tr)
  | ξ_concatenate₂ norm₁ tr ih => 
      cases tr' with
      | ξ_concatenate₂ norm₁' tr' => rw [ih tr']
      | ξ_concatenate₁ tr' => exact Empty.elim (norm₁.does_not_reduce tr')
      | β_concatenate norm₁' norm₂' => exact Empty.elim (norm₂'.does_not_reduce tr)
  | β_concatenate norm₁ norm₂ =>
      cases tr' with
      | β_concatenate norm₁' norm₂' => rfl
      | ξ_concatenate₁ tr' => exact Empty.elim (norm₁.does_not_reduce tr')
      | ξ_concatenate₂ norm₁' tr' => exact Empty.elim (norm₂.does_not_reduce tr')
  | ξ_length tr ih => 
      cases tr' with
      | ξ_length tr' => rw [ih tr']
      | β_length norm' => exact Empty.elim (norm'.does_not_reduce tr)
  | β_length norm =>
      cases tr' with
      | β_length norm' => rfl
      | ξ_length tr' => exact Empty.elim (norm.does_not_reduce tr')
  | ξ_let tr ih =>
      cases tr' with
      | ξ_let tr' => rw [ih tr']
      | β_let h norm' => exact Empty.elim (norm'.does_not_reduce tr)
  | β_let h norm =>
      cases tr' with
      | β_let h' norm' => rw [h, h']
      | ξ_let tr' => exact Empty.elim (norm.does_not_reduce tr')

end Transition

namespace Transitionᵣₜ

theorem deterministic
  {Γ : Context} {τ : Ty} {t₁ t₂ t₂' : Γ ⊢ τ}
  (mtr : t₁ ⟶* t₂) (mtr' : t₁ ⟶* t₂')
  (norm₂ : Normal t₂) (norm₂' : Normal t₂') :
  t₂ = t₂' :=
  match mtr, mtr' with
  | .refl _, .refl _ => rfl
  | .refl _, .trans _ tr' _ => Empty.elim (Normal.does_not_reduce norm₂ tr')
  | .trans _ tr _, .refl _ => Empty.elim (Normal.does_not_reduce norm₂' tr)
  | .trans _ tr mtr, .trans _ tr' mtr' => by
      rw [Transition.deterministic tr tr'] at mtr
      exact deterministic mtr mtr' norm₂ norm₂'

theorem confluent
  {Γ : Context} {τ : Ty} {t₁ t₂ t₂' : Γ ⊢ τ}
  (mtr : t₁ ⟶* t₂) (mtr' : t₁ ⟶* t₂') :
  Σ t₃ : Γ ⊢ τ, (t₂ ⟶* t₃) × (t₂' ⟶* t₃) := by
  cases mtr with
  | refl _ =>
      cases mtr' with
      | refl _ => exact ⟨t₁, Transitionᵣₜ.refl _, Transitionᵣₜ.refl _⟩
      | trans _ tr' mtr' => exact ⟨t₂', Transitionᵣₜ.trans _ tr' mtr', Transitionᵣₜ.refl _⟩
  | trans _ tr mtr =>
      cases mtr' with
      | refl _ => exact ⟨t₂, Transitionᵣₜ.refl _, Transitionᵣₜ.trans _ tr mtr⟩
      | trans _ tr' mtr' =>
          have := Transition.deterministic tr tr'
          subst this
          exact confluent mtr mtr'

theorem diamond
  {Γ : Context} {τ : Ty} {t₁ t₂ t₂' : Γ ⊢ τ}
  (tr : t₁ ⟶ t₂) (tr' : t₁ ⟶ t₂') :
  Σ t₃ : Γ ⊢ τ, (t₂ ⟶* t₃) × (t₂' ⟶* t₃) :=
  confluent (Transitionᵣₜ.trans _ tr (Transitionᵣₜ.refl _)) (Transitionᵣₜ.trans _ tr' (Transitionᵣₜ.refl _))

end Transitionᵣₜ
