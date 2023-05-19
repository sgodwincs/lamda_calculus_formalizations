import Aesop

import Prod1.Dynamics.Normal
import Prod1.Statics

open Statics

namespace Dynamics

inductive Transition {Γ : Context} : {τ : Ty} → (Γ ⊢ τ) → (Γ ⊢ τ) → Type where
  | ξ_pair₁
      {τ₁ τ₂ : Ty} {e₁ e₁' : Γ ⊢ τ₁} {e₂ : Γ ⊢ τ₂} :
      Transition e₁ e₁' →
      Transition (Expr.pair e₁ e₂) (Expr.pair e₁' e₂)

  | ξ_pair₂
      {τ₁ τ₂ : Ty} {e₁ : Γ ⊢ τ₁} {e₂ e₂' : Γ ⊢ τ₂} :
      Normal e₁ →
      Transition e₂ e₂' →
      Transition (Expr.pair e₁ e₂) (Expr.pair e₁ e₂')

  | ξ_proj₁
      {τ₁ τ₂ : Ty} {e e' : Γ ⊢ Ty.prod τ₁ τ₂} :
      Transition e e' →
      Transition (Expr.proj₁ e) (Expr.proj₁ e')
  
  | β_proj₁
      {τ₁ τ₂ : Ty} {e₁ : Γ ⊢ τ₁} {e₂ : Γ ⊢ τ₂} :
      Value e₁ →
      Value e₂ →
      Transition (Expr.proj₁ (Expr.pair e₁ e₂)) e₁

  | ξ_proj₂
      {τ₁ τ₂ : Ty} {e e' : Γ ⊢ Ty.prod τ₁ τ₂} :
      Transition e e' →
      Transition (Expr.proj₂ e) (Expr.proj₂ e')
  
  | β_proj₂
      {τ₁ τ₂ : Ty} {e₁ : Γ ⊢ τ₁} {e₂ : Γ ⊢ τ₂} :
      Value e₁ →
      Value e₂ →
      Transition (Expr.proj₂ (Expr.pair e₁ e₂)) e₂

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
  Transitionᵣₜ.trans _ tr (Transitionᵣₜ.trans _ tr' (Transitionᵣₜ.refl _))

instance {Γ : Context} {τ : Ty} : Trans (@Transition Γ τ) (@Transitionᵣₜ Γ τ) Transitionᵣₜ where
  trans := Transitionᵣₜ.trans_tr_mtr

instance {Γ : Context} {τ : Ty} : Trans (@Transitionᵣₜ Γ τ) (@Transition Γ τ) Transitionᵣₜ where
  trans := Transitionᵣₜ.trans_mtr_tr 

instance {Γ : Context} {τ : Ty} : Trans (@Transitionᵣₜ Γ τ) (@Transitionᵣₜ Γ τ) Transitionᵣₜ where
  trans := Transitionᵣₜ.trans'

instance {Γ : Context} {τ : Ty} : Trans (@Transition Γ τ) (@Transition Γ τ) Transitionᵣₜ where
  trans := Transition.trans

namespace Transitionᵣₜ

def ξ_pair₁
  {Γ : Context} {τ₁ τ₂ : Ty} {e₁ e₁' : Γ ⊢ τ₁} {e₂ : Γ ⊢ τ₂} :
  (e₁ ⟶* e₁') →
  (Expr.pair e₁ e₂ ⟶* Expr.pair e₁' e₂)
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr mtr =>
      calc
        _ ⟶ (Expr.pair _ _) := Transition.ξ_pair₁ tr
        _ ⟶* _ := ξ_pair₁ mtr

def ξ_pair₂
  {Γ : Context} {τ₁ τ₂ : Ty} {e₁ : Γ ⊢ τ₁} {e₂ e₂' : Γ ⊢ τ₂}
  (norm₁ : Normal e₁) :
  (e₂ ⟶* e₂') →
  (Expr.pair e₁ e₂ ⟶* Expr.pair e₁ e₂')
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr mtr =>
      calc
        _ ⟶ (Expr.pair _ _) := Transition.ξ_pair₂ norm₁ tr
        _ ⟶* _ := ξ_pair₂ norm₁ mtr

def ξ_proj₁
  {Γ : Context} {τ₁ τ₂ : Ty} {e e' : Γ ⊢ Ty.prod τ₁ τ₂} :
  (e ⟶* e') →
  (Expr.proj₁ e ⟶* Expr.proj₁ e')
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr mtr =>
      calc
        _ ⟶ (Expr.proj₁ _) := Transition.ξ_proj₁ tr
        _ ⟶* _ := ξ_proj₁ mtr

def ξ_proj₂
  {Γ : Context} {τ₁ τ₂ : Ty} {e e' : Γ ⊢ Ty.prod τ₁ τ₂} :
  (e ⟶* e') →
  (Expr.proj₂ e ⟶* Expr.proj₂ e')
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr mtr =>
      calc
        _ ⟶ (Expr.proj₂ _) := Transition.ξ_proj₂ tr
        _ ⟶* _ := ξ_proj₂ mtr

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
  | .triv => Sum.inl Value.triv.normal
  | .pair e₁ e₂ =>
      match e₁.normal_or_reduces, e₂.normal_or_reduces with
      | .inl (.value val₁), .inl (.value val₂) => Sum.inl (Value.pair val₁ val₂).normal
      | .inl (.neutral neut₁), .inl norm₂ => Sum.inl (Neutral.pair₁ neut₁ norm₂).normal
      | .inl (.value val₁), .inl (.neutral neut₂) => Sum.inl (Neutral.pair₂ val₁ neut₂).normal
      | .inr ⟨_, tr₁⟩, _ => Sum.inr ⟨_, Transition.ξ_pair₁ tr₁⟩
      | .inl norm₁, .inr ⟨_, tr₂⟩ => Sum.inr ⟨_, Transition.ξ_pair₂ norm₁ tr₂⟩
  | .proj₁ e =>
      match e.normal_or_reduces with
      | .inl (.value (Value.pair val₁ val₂)) => Sum.inr ⟨_, Transition.β_proj₁ val₁ val₂⟩
      | .inl (.neutral neut) => Sum.inl (Neutral.proj₁ neut).normal
      | .inr ⟨_, tr⟩ => Sum.inr ⟨_, Transition.ξ_proj₁ tr⟩
  | .proj₂ e =>
      match e.normal_or_reduces with
      | .inl (.value (Value.pair val₁ val₂)) => Sum.inr ⟨_, Transition.β_proj₂ val₁ val₂⟩
      | .inl (.neutral neut) => Sum.inl (Neutral.proj₂ neut).normal
      | .inr ⟨_, tr⟩ => Sum.inr ⟨_, Transition.ξ_proj₂ tr⟩
  | .abstraction _ => Sum.inl Value.abstraction.normal
  | .application e₁ e₂ =>
      match e₁.normal_or_reduces, e₂.normal_or_reduces with
      | .inl (.value .abstraction), .inl norm => Sum.inr ⟨_, Transition.β_application rfl norm⟩
      | .inl (.neutral neut₁), .inl norm₂ => Sum.inl (Neutral.application neut₁ norm₂).normal
      | .inl norm₁, .inr ⟨_, tr₂⟩ => Sum.inr ⟨_, Transition.ξ_application₂ norm₁ tr₂⟩
      | .inr ⟨_, tr₁⟩, _ => Sum.inr ⟨_, Transition.ξ_application₁ tr₁⟩

def Value.does_not_reduce
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ} :
  Value e →
  (e ⟶ e') →
  Empty
  | .triv, tr => nomatch tr
  | .pair val₁ _, .ξ_pair₁ tr₁ => val₁.does_not_reduce tr₁
  | .pair _ val₂, .ξ_pair₂ norm₁ tr₂ => val₂.does_not_reduce tr₂
  | .abstraction, tr => nomatch tr

mutual

theorem Normal.does_not_reduce
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ} :
  (norm : Normal e) →
  (tr : e ⟶ e') →
  Empty
  | .value val, tr => val.does_not_reduce tr
  | .neutral neut, tr => neut.does_not_reduce tr

theorem Neutral.does_not_reduce
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ}
  (neut : Neutral e)
  (tr : e ⟶ e') :
  Empty :=
  match neut with
  | .pair₁ neut₁ norm₂ => by
      cases tr with
      | ξ_pair₁ tr₁ => exact neut₁.does_not_reduce tr₁
      | ξ_pair₂ _ tr₂ => exact norm₂.does_not_reduce tr₂
  | .pair₂ val₁ neut₂ => by
      cases tr with
      | ξ_pair₁ tr₁ => exact val₁.does_not_reduce tr₁
      | ξ_pair₂ norm₁ tr₂ => exact neut₂.does_not_reduce tr₂
  | .proj₁ neut => by
      cases tr with
      | ξ_proj₁ tr => exact neut.does_not_reduce tr
      | β_proj₁ val₁ val₂ =>
          cases neut with
          | pair₁ neut₁ _ => exact val₁.not_neutral neut₁
          | pair₂ _ neut₂ => exact val₂.not_neutral neut₂ 
  | .proj₂ neut => by
      cases tr with
      | ξ_proj₂ tr => exact neut.does_not_reduce tr
      | β_proj₂ val₁ val₂ =>
          cases neut with
          | pair₁ neut₁ _ => exact val₁.not_neutral neut₁
          | pair₂ _ neut₂ => exact val₂.not_neutral neut₂ 
  | .application neut₁ norm₂ =>
      match tr with
      | .ξ_application₁ tr₁ => neut₁.does_not_reduce tr₁
      | .ξ_application₂ _ tr₂ => norm₂.does_not_reduce tr₂
      | .β_application _ _ => nomatch neut₁

end

namespace Transition

theorem irrelevant
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ}
  (tr tr' : e ⟶ e') :
  tr = tr' :=
by
  match τ, e, e', tr with
  | _, _, _, .ξ_pair₁ tr₁ =>
      cases tr' with
      | ξ_pair₁ tr₁' => rw [irrelevant tr₁ tr₁']
      | ξ_pair₂ norm₁' tr₂' => exact Empty.elim (norm₁'.does_not_reduce tr₁)
  | _, _, _, .ξ_pair₂ norm₁ tr₂ =>
      cases tr' with
      | ξ_pair₁ tr₁' => exact Empty.elim (norm₁.does_not_reduce tr₁')
      | ξ_pair₂ norm₁' tr₂' => rw [Normal.irrelevant norm₁ norm₁', irrelevant tr₂ tr₂']
  | _, _, _, .ξ_proj₁ tr =>
      cases tr' with
      | ξ_proj₁ tr₁' => rw [irrelevant tr tr₁']
      | β_proj₁ val₁' val₂' =>
          cases tr with
          | ξ_pair₁ tr₁ => exact Empty.elim (val₁'.does_not_reduce tr₁)
  | _, _, _, .β_proj₁ val₁ val₂ =>
      cases tr' with
      | ξ_proj₁ tr' =>
          cases tr' with
          | ξ_pair₁ tr₁' => exact Empty.elim (val₁.does_not_reduce tr₁')
      | β_proj₁ val₁' val₂' => rw [Value.irrelevant val₁ val₁', Value.irrelevant val₂ val₂']
  | _, _, _, .ξ_proj₂ tr =>
      cases tr' with
      | ξ_proj₂ tr₁' => rw [irrelevant tr tr₁']
      | β_proj₂ val₁' val₂' =>
          cases tr with
          | ξ_pair₂ val₁ tr₂ => exact Empty.elim (val₂'.does_not_reduce tr₂)
  | _, _, _, .β_proj₂ val₁ val₂ =>
      cases tr' with
      | ξ_proj₂ tr' =>
          cases tr' with
          | ξ_pair₂ val₁' tr₂' => exact Empty.elim (val₂.does_not_reduce tr₂')
      | β_proj₂ val₁' val₂' => rw [Value.irrelevant val₁ val₁', Value.irrelevant val₂ val₂']
  | _, _, _, .ξ_application₁ tr₁ =>
      cases tr' with
      | ξ_application₁ tr₁' => rw [irrelevant tr₁ tr₁']
      | ξ_application₂ norm₁' tr₂' => exact Empty.elim (norm₁'.does_not_reduce tr₁)
      | β_application h' norm₂' => exact nomatch tr₁
  | _, _, _, .ξ_application₂ norm₁ tr₂ =>
      cases tr' with
      | ξ_application₁ tr₁' => exact Empty.elim (norm₁.does_not_reduce tr₁')
      | ξ_application₂ norm₁' tr₂' => rw [Normal.irrelevant norm₁ norm₁', irrelevant tr₂ tr₂']
      | β_application h' norm₂' => exact Empty.elim (norm₂'.does_not_reduce tr₂)
  | _, _, _, .β_application h norm₂ =>
      cases tr' with
      | ξ_application₁ tr₁' => exact nomatch tr₁'
      | ξ_application₂ norm₁' tr₂' => exact Empty.elim (norm₂.does_not_reduce tr₂')
      | β_application h' norm₂' => rw [Normal.irrelevant norm₂ norm₂']

termination_by irrelevant => sizeOf tr

theorem deterministic
  {Γ : Context} {τ : Ty} {e₁ e₂ e₂' : Γ ⊢ τ}
  (tr : e₁ ⟶ e₂)
  (tr' : e₁ ⟶ e₂') : 
  e₂ = e₂' :=
by
  match τ, e₁, e₂, tr with
  | _, _, _, .ξ_pair₁ tr₁ =>
      cases tr' with
      | ξ_pair₁ tr₁' => rw [deterministic tr₁ tr₁']
      | ξ_pair₂ norm₁' tr₂' => exact Empty.elim (norm₁'.does_not_reduce tr₁)
  | _, _, _, .ξ_pair₂ norm₁ tr₂ =>
      cases tr' with
      | ξ_pair₁ tr₁' => exact Empty.elim (norm₁.does_not_reduce tr₁')
      | ξ_pair₂ norm₁' tr₂' => rw [deterministic tr₂ tr₂']
  | _, _, _, .ξ_proj₁ tr =>
      cases tr' with
      | ξ_proj₁ tr₁' => rw [deterministic tr tr₁']
      | β_proj₁ val₁' val₂' =>
          cases tr with
          | ξ_pair₁ tr₁ => exact Empty.elim (val₁'.does_not_reduce tr₁)
          | ξ_pair₂ norm₁ tr₂ => exact Empty.elim (val₂'.does_not_reduce tr₂)
  | _, _, _, .β_proj₁ val₁ val₂ =>
      cases tr' with
      | ξ_proj₁ tr' =>
          cases tr' with
          | ξ_pair₁ tr₁' => exact Empty.elim (val₁.does_not_reduce tr₁')
          | ξ_pair₂ norm₁' tr₂' => exact Empty.elim (val₂.does_not_reduce tr₂')
      | β_proj₁ val₁' val₂' => rfl
  | _, _, _, .ξ_proj₂ tr =>
      cases tr' with
      | ξ_proj₂ tr₂' => rw [deterministic tr tr₂']
      | β_proj₂ val₁' val₂' =>
          cases tr with
          | ξ_pair₁ tr₁ => exact Empty.elim (val₁'.does_not_reduce tr₁)
          | ξ_pair₂ norm₁ tr₂ => exact Empty.elim (val₂'.does_not_reduce tr₂)
  | _, _, _, .β_proj₂ val₁ val₂ =>
      cases tr' with
      | ξ_proj₂ tr' =>
          cases tr' with
          | ξ_pair₁ tr₁' => exact Empty.elim (val₁.does_not_reduce tr₁')
          | ξ_pair₂ norm₁' tr₂' => exact Empty.elim (val₂.does_not_reduce tr₂')
      | β_proj₂ val₁' val₂' => rfl
  | _, _, _, .ξ_application₁ tr₁ =>
      cases tr' with
      | ξ_application₁ tr₁' => rw [deterministic tr₁ tr₁']
      | ξ_application₂ norm₁' tr₂' => exact Empty.elim (norm₁'.does_not_reduce tr₁)
      | β_application h' norm₂' => exact nomatch tr₁
  | _, _, _, .ξ_application₂ norm₁ tr₂ =>
      cases tr' with
      | ξ_application₁ tr₁' => exact Empty.elim (norm₁.does_not_reduce tr₁')
      | ξ_application₂ norm₁' tr₂' => rw [deterministic tr₂ tr₂']
      | β_application h' norm₂' => exact Empty.elim (norm₂'.does_not_reduce tr₂)
  | _, _, _, .β_application h norm₂ =>
      cases tr' with
      | ξ_application₁ tr₁' => exact nomatch tr₁'
      | ξ_application₂ norm₁' tr₂' => exact Empty.elim (norm₂.does_not_reduce tr₂')
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
  | .refl _, .trans _ tr' _ => Empty.elim (norm₂.does_not_reduce tr')
  | .trans _ tr _, .refl _ => Empty.elim (norm₂'.does_not_reduce tr)
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
