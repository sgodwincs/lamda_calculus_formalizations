import Aesop

import EF.Dynamics.Normal
import EF.Statics

open Statics

namespace Dynamics

inductive Transition {Γ : Context} : {τ : Ty} → (Γ ⊢ τ) → (Γ ⊢ τ) → Type where
  | ξ_application₁
      {τ τ' : Ty} {e₁ e₁' : Γ ⊢ Ty.arrow τ τ'} {e₂ : Γ ⊢ τ} :
      Transition e₁ e₁' →
      Transition (Expr.application e₁ e₂) (Expr.application e₁' e₂)

  | ξ_application₂
      {τ τ' : Ty} {e₁ : Γ ⊢ Ty.arrow τ τ'} {e₂ e₂' : Γ ⊢ τ} :
      Normal e₁ →
      Transition e₂ e₂' →
      Transition (Expr.application e₁ e₂) (Expr.application e₁ e₂')
  
  | β_application
      {τ τ' : Ty} {e₁' : τ :: Γ ⊢ τ'} {e₂ : Γ ⊢ τ} {e' : Γ ⊢ τ'} :
      e' = e₁' [ e₂ ] →
      Normal e₂ →
      Transition (Expr.application (Expr.abstraction e₁') e₂) e'
  deriving DecidableEq

notation:40 e₁ " ⟶ " e₂ => Transition e₁ e₂

inductive Transitionᵣₜ {Γ : Context} : {τ : Ty} → (Γ ⊢ τ) → (Γ ⊢ τ) → Type where
  | refl
      {τ : Ty} :
      (e : Γ ⊢ τ) →
      Transitionᵣₜ e e
  
  | trans
      {τ : Ty}
      (e : Γ ⊢ τ) {e' e'' : Γ ⊢ τ} :
      (e ⟶ e') →
      Transitionᵣₜ e' e'' →
      Transitionᵣₜ e e''
  deriving DecidableEq

notation:20 e₁ " ⟶* " e₂ => Transitionᵣₜ e₁ e₂

namespace Transitionᵣₜ

def trans_tr_mtr
  {Γ : Context} {τ : Ty} {e e' e'' : Γ ⊢ τ}
  (tr : e ⟶ e') (mtr' : e' ⟶* e'') : (e ⟶* e'') := Transitionᵣₜ.trans _ tr mtr'

def trans_mtr_tr
  {Γ : Context} {τ : Ty} {e e' e'' : Γ ⊢ τ} :
  (e ⟶* e') → (e' ⟶ e'') → (e ⟶* e'')
  | .refl _, tr' => Transitionᵣₜ.trans _ tr' (Transitionᵣₜ.refl _)
  | .trans _ tr mtr, tr' => Transitionᵣₜ.trans _ tr (trans_mtr_tr mtr tr')

def trans'
  {Γ : Context} {τ : Ty} {e e' e'' : Γ ⊢ τ} :
  (e ⟶* e') → (e' ⟶* e'') → (e ⟶* e'')
  | .refl _, mtr' => mtr'
  | .trans _ tr mtr, mtr' => Transitionᵣₜ.trans _ tr (trans' mtr mtr')

end Transitionᵣₜ

def Transition.trans
  {Γ : Context} {τ : Ty} {e e' e'' : Γ ⊢ τ}
  (tr : e ⟶ e') (tr' : e' ⟶ e'') : (e ⟶* e'') :=
  match τ, e, e', tr with
  | .(_), .(_), .(_), .ξ_application₁ tr₁ => Transitionᵣₜ.trans _ (Transition.ξ_application₁ tr₁)
      (match tr' with
      | .ξ_application₁ tr₁' => Transitionᵣₜ.trans _ (Transition.ξ_application₁ tr₁') (Transitionᵣₜ.refl _)
      | .ξ_application₂ norm₁' tr₂' => Transitionᵣₜ.trans _ (Transition.ξ_application₂ norm₁' tr₂') (Transitionᵣₜ.refl _)
      | .β_application norm₁' norm₂' => Transitionᵣₜ.trans _ (Transition.β_application norm₁' norm₂') (Transitionᵣₜ.refl _))
  | .(_), .(_), .(_), .ξ_application₂ norm₁ tr₂ => Transitionᵣₜ.trans _ (Transition.ξ_application₂ norm₁ tr₂)
      (match tr' with
      | .ξ_application₁ tr₁' => Transitionᵣₜ.trans _ (Transition.ξ_application₁ tr₁') (Transitionᵣₜ.refl _)
      | .ξ_application₂ norm₁' tr₂' => Transitionᵣₜ.trans _ (Transition.ξ_application₂ norm₁' tr₂') (Transitionᵣₜ.refl _)
      | .β_application norm₁' norm₂' => Transitionᵣₜ.trans _ (Transition.β_application norm₁' norm₂') (Transitionᵣₜ.refl _))
  | .(_), .(_), .(_), .β_application h norm₂ => Transitionᵣₜ.trans _ (Transition.β_application h norm₂) (Transitionᵣₜ.trans_tr_mtr tr' (Transitionᵣₜ.refl _))

instance {Γ : Context} {τ : Ty} : Trans (@Transition Γ τ) (@Transitionᵣₜ Γ τ) Transitionᵣₜ where
  trans := Transitionᵣₜ.trans_tr_mtr

instance {Γ : Context} {τ : Ty} : Trans (@Transitionᵣₜ Γ τ) (@Transition Γ τ) Transitionᵣₜ where
  trans := Transitionᵣₜ.trans_mtr_tr 

instance {Γ : Context} {τ : Ty} : Trans (@Transitionᵣₜ Γ τ) (@Transitionᵣₜ Γ τ) Transitionᵣₜ where
  trans := Transitionᵣₜ.trans'

instance {Γ : Context} {τ : Ty} : Trans (@Transition Γ τ) (@Transition Γ τ) Transitionᵣₜ where
  trans := Transition.trans

namespace Transitionᵣₜ

def ξ_application₁
  {Γ : Context} {τ τ' : Ty} {e₁ e₁' : Γ ⊢ Ty.arrow τ τ'} {e₂ : Γ ⊢ τ} :
  (e₁ ⟶* e₁') →
  (Expr.application e₁ e₂ ⟶* Expr.application e₁' e₂)
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr₁ mtr₁ =>
      calc
        _ ⟶ (Expr.application _ _) := Transition.ξ_application₁ tr₁
        _ ⟶* _ := ξ_application₁ mtr₁

def ξ_application₂
  {Γ : Context} {τ τ' : Ty} {e₁ : Γ ⊢ Ty.arrow τ τ'} {e₂ e₂' : Γ ⊢ τ}
  (norm₁ : Normal e₁) :
  (e₂ ⟶* e₂') →
  (Expr.application e₁ e₂ ⟶* Expr.application e₁ e₂')
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr₂ mtr₂ =>
      calc
        _ ⟶ (Expr.application _ _) := Transition.ξ_application₂ norm₁ tr₂
        _ ⟶* _ := ξ_application₂ norm₁ mtr₂

def length
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ} :
  (e ⟶* e') → Nat
  | .refl _ => 0
  | .trans _ _ mtr => 1 + length mtr

end Transitionᵣₜ

def _root_.Statics.Expr.normal_or_reduces
  {Γ : Context} {τ : Ty} :
  (e : Γ ⊢ τ) → 
  Sum (Normal e) (Σ e' : Γ ⊢ τ, e ⟶ e')
  | .var i => Sum.inl (Neutral.var i).normal
  | .number _ => Sum.inl Value.number.normal
  | .string _ => Sum.inl Value.string.normal
  | .abstraction _ => Sum.inl Value.abstraction.normal
  | .application e₁ e₂ =>
      match e₁.normal_or_reduces, e₂.normal_or_reduces with
      | .inl (.value .abstraction), .inl norm => Sum.inr ⟨_, Transition.β_application rfl norm⟩
      | .inl (.value .abstraction), .inr ⟨_, tr₂⟩ => Sum.inr ⟨_, Transition.ξ_application₂ Value.abstraction.normal tr₂⟩
      | .inl (.neutral neut₁), .inl norm₂ => Sum.inl (Neutral.application neut₁ norm₂).normal
      | .inl (.neutral neut₁), .inr ⟨_, tr₂⟩ => Sum.inr ⟨_, Transition.ξ_application₂ neut₁.normal tr₂⟩
      | .inr ⟨_, tr₁⟩, _ => Sum.inr ⟨_, Transition.ξ_application₁ tr₁⟩

def Value.does_not_reduce
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ} :
  Value e →
  (e ⟶ e') →
  Empty
  | .number, tr => nomatch tr
  | .string, tr => nomatch tr
  | .abstraction, tr => nomatch tr

mutual

theorem Normal.does_not_reduce
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ} :
  (norm : Normal e) →
  (tr : e ⟶ e') →
  Empty
  | .value val, tr => Value.does_not_reduce val tr
  | .neutral neut, tr => Neutral.does_not_reduce neut tr

theorem Neutral.does_not_reduce
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ}
  (neut : Neutral e)
  (tr : e ⟶ e') :
  Empty :=
  match neut with
  | .application neut₁ norm₂ =>
      match tr with
      | .ξ_application₁ tr₁ => Neutral.does_not_reduce neut₁ tr₁
      | .ξ_application₂ norm₁ tr₂ => Normal.does_not_reduce norm₂ tr₂
      | .β_application h norm₂' => nomatch neut₁

end

namespace Transition

theorem irrelevant
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ}
  (tr tr' : e ⟶ e') :
  tr = tr' :=
by
  cases tr with
  | ξ_application₁ tr₁ =>
      cases tr' with
      | ξ_application₁ tr₁' => rw [irrelevant tr₁ tr₁']
      | ξ_application₂ norm₁' tr₂' => exact Empty.elim (Normal.does_not_reduce norm₁' tr₁)
      | β_application h' norm₂' => exact nomatch tr₁
  | ξ_application₂ norm₁ tr₂ =>
      cases tr' with
      | ξ_application₁ tr₁' => exact Empty.elim (Normal.does_not_reduce norm₁ tr₁')
      | ξ_application₂ norm₁' tr₂' => rw [Normal.irrelevant norm₁ norm₁', irrelevant tr₂ tr₂']
      | β_application h' norm₂' => exact Empty.elim (Normal.does_not_reduce norm₂' tr₂)
  | β_application h norm₂ =>
      cases tr' with
      | ξ_application₁ tr₁' => exact nomatch tr₁'
      | ξ_application₂ norm₁' tr₂' => exact Empty.elim (Normal.does_not_reduce norm₂ tr₂')
      | β_application h' norm₂' => rw [Normal.irrelevant norm₂ norm₂']

theorem deterministic
  {Γ : Context} {τ : Ty} {e₁ e₂ e₂' : Γ ⊢ τ}
  (tr : e₁ ⟶ e₂)
  (tr' : e₁ ⟶ e₂') : 
  e₂ = e₂' :=
by
  cases tr with
  | ξ_application₁ tr₁ =>
      cases tr' with
      | ξ_application₁ tr₁' => rw [deterministic tr₁ tr₁']
      | ξ_application₂ norm₁' tr₂' => exact Empty.elim (Normal.does_not_reduce norm₁' tr₁)
      | β_application h' norm₂' => exact nomatch tr₁
  | ξ_application₂ norm₁ tr₂ =>
      cases tr' with
      | ξ_application₁ tr₁' => exact Empty.elim (Normal.does_not_reduce norm₁ tr₁')
      | ξ_application₂ norm₁' tr₂' => rw [deterministic tr₂ tr₂']
      | β_application h' norm₂' => exact Empty.elim (Normal.does_not_reduce norm₂' tr₂)
  | β_application h norm₂ =>
      cases tr' with
      | ξ_application₁ tr₁' => exact nomatch tr₁'
      | ξ_application₂ norm₁' tr₂' => exact Empty.elim (Normal.does_not_reduce norm₂ tr₂')
      | β_application h' norm₂' => subst_vars; rfl

end Transition

namespace Transitionᵣₜ

theorem deterministic
  {Γ : Context} {τ : Ty} {e₁ e₂ e₂' : Γ ⊢ τ}
  (mtr : e₁ ⟶* e₂) (mtr' : e₁ ⟶* e₂')
  (norm₂ : Normal e₂) (norm₂' : Normal e₂') :
  e₂ = e₂' :=
  match mtr, mtr' with
  | .refl _, .refl _ => rfl
  | .refl _, .trans _ tr' _ => Empty.elim (Normal.does_not_reduce norm₂ tr')
  | .trans _ tr _, .refl _ => Empty.elim (Normal.does_not_reduce norm₂' tr)
  | .trans _ tr mtr, .trans _ tr' mtr' => by
      rw [Transition.deterministic tr tr'] at mtr
      exact deterministic mtr mtr' norm₂ norm₂'

theorem confluent
  {Γ : Context} {τ : Ty} {e₁ e₂ e₂' : Γ ⊢ τ}
  (mtr : e₁ ⟶* e₂) (mtr' : e₁ ⟶* e₂') :
  Σ t₃ : Γ ⊢ τ, (e₂ ⟶* t₃) × (e₂' ⟶* t₃) := by
  cases mtr with
  | refl _ =>
      cases mtr' with
      | refl _ => exact ⟨e₁, Transitionᵣₜ.refl _, Transitionᵣₜ.refl _⟩
      | trans _ tr' mtr' => exact ⟨e₂', Transitionᵣₜ.trans _ tr' mtr', Transitionᵣₜ.refl _⟩
  | trans _ tr mtr =>
      cases mtr' with
      | refl _ => exact ⟨e₂, Transitionᵣₜ.refl _, Transitionᵣₜ.trans _ tr mtr⟩
      | trans _ tr' mtr' =>
          have := Transition.deterministic tr tr'
          subst this
          exact confluent mtr mtr'

theorem diamond
  {Γ : Context} {τ : Ty} {e₁ e₂ e₂' : Γ ⊢ τ}
  (tr : e₁ ⟶ e₂) (tr' : e₁ ⟶ e₂') :
  Σ e₃ : Γ ⊢ τ, (e₂ ⟶* e₃) × (e₂' ⟶* e₃) :=
  confluent (Transitionᵣₜ.trans _ tr (Transitionᵣₜ.refl _)) (Transitionᵣₜ.trans _ tr' (Transitionᵣₜ.refl _))

end Transitionᵣₜ
