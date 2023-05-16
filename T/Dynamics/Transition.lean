import Aesop

import T.Dynamics.Normal
import T.Statics

open Statics

namespace Dynamics

inductive Transition {Γ : Context} : {τ : Ty} → (Γ ⊢ τ) → (Γ ⊢ τ) → Type where
  | ξ_succ
      {e e' : Γ ⊢ Ty.nat} :
      Transition e e' →
      Transition (Expr.succ e) (Expr.succ e')
  
  | ξ_recursor
      {τ : Ty} {e e' : Γ ⊢ Ty.nat} {e₀ : Γ ⊢ τ} {eₛ : τ :: Ty.nat :: Γ ⊢ τ} :
      Transition e e' →
      Transition (Expr.recursor e e₀ eₛ) (Expr.recursor e' e₀ eₛ)
  
  | β_recursor₀
      {τ : Ty} {e₀ : Γ ⊢ τ} {eₛ : τ :: Ty.nat :: Γ ⊢ τ} :
      Transition (Expr.recursor Expr.zero e₀ eₛ) e₀
  
  | β_recursorₛ
      {τ : Ty} {e : Γ ⊢ Ty.nat} {e₀ : Γ ⊢ τ} {eₛ : τ :: Ty.nat :: Γ ⊢ τ} {e' : Γ ⊢ τ}:
      e' = (⟪ Expr.recursor e e₀ eₛ • e • Subst.ids ⟫) eₛ →
      Value e →
      Transition (Expr.recursor (Expr.succ e) e₀ eₛ) e'

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

def ξ_succ
  {Γ : Context} {e e' : Γ ⊢ Ty.nat} :
  (e ⟶* e') →
  (Expr.succ e ⟶* Expr.succ e')
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr mtr =>
      calc
        _ ⟶ (Expr.succ _) := Transition.ξ_succ tr
        _ ⟶* _ := ξ_succ mtr

def ξ_recursor
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ Ty.nat} {e₀ : Γ ⊢ τ} {eₛ : τ :: Ty.nat :: Γ ⊢ τ} :
  (e ⟶* e') →
  (Expr.recursor e e₀ eₛ ⟶* Expr.recursor e' e₀ eₛ)
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr mtr =>
      calc
        _ ⟶ (Expr.recursor _ _ _) := Transition.ξ_recursor tr
        _ ⟶* _ := ξ_recursor mtr

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
  | .zero => Sum.inl Value.zero.normal
  | .succ e =>
      match e.normal_or_reduces with
      | .inl (.value val) => Sum.inl (Value.succ val).normal
      | .inl (.neutral neut) => Sum.inl (Neutral.succ neut).normal
      | .inr ⟨_, tr⟩ => Sum.inr ⟨_, Transition.ξ_succ tr⟩
  | .recursor e _ _ =>
      match e.normal_or_reduces with
      | .inl (.value .zero) => Sum.inr ⟨_, Transition.β_recursor₀⟩
      | .inl (.value (Value.succ val)) => Sum.inr ⟨_, Transition.β_recursorₛ rfl val⟩
      | .inl (.neutral neut) => Sum.inl (Neutral.recursor neut).normal
      | .inr ⟨_, tr⟩ => Sum.inr ⟨_, Transition.ξ_recursor tr⟩
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
  | .zero, tr => nomatch tr
  | .succ val, .ξ_succ tr => val.does_not_reduce tr
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
  | .succ neut =>
      match tr with
      | .ξ_succ tr => neut.does_not_reduce tr
  | .recursor neut =>
      match tr with
      | .ξ_recursor tr => neut.does_not_reduce tr
      | .β_recursor₀ => nomatch neut
      | .β_recursorₛ _ val =>
          let .succ neut := neut
          val.not_neutral neut
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
  | _, _, _, .ξ_succ tr =>
      cases tr' with
      | ξ_succ tr' => rw [irrelevant tr tr']
  | _, _, _, .ξ_recursor tr =>
      cases tr' with
      | ξ_recursor tr' => rw [irrelevant tr tr']
      | β_recursorₛ _ val' =>
          cases tr
          rename_i tr _
          exact Empty.elim (val'.does_not_reduce tr)
  | _, _, _, .β_recursor₀ => cases tr'; rfl
  | _, _, _, .β_recursorₛ _ val =>
      cases tr' with
      | ξ_recursor tr' =>
          cases tr'
          rename_i tr' _
          exact Empty.elim (val.does_not_reduce tr')
      | β_recursorₛ _ val' => rw [Value.irrelevant val val']
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
  | _, _, _, .ξ_succ tr =>
      cases tr' with
      | ξ_succ tr' => rw [deterministic tr tr']
  | _, _, _, .ξ_recursor tr =>
      cases tr' with
      | ξ_recursor tr' => rw [deterministic tr tr']
      | β_recursor₀ => exact nomatch tr
      | β_recursorₛ _ val' =>
          cases tr
          rename_i tr
          exact Empty.elim (val'.does_not_reduce tr)
  | _, _, _, .β_recursor₀ =>
      cases tr' with
      | ξ_recursor tr' => exact nomatch tr'
      | β_recursor₀ => rfl
  | _, _, _, .β_recursorₛ _ val =>
      cases tr' with
      | ξ_recursor tr' =>
          cases tr'
          rename_i tr'
          exact Empty.elim (val.does_not_reduce tr')
      | β_recursorₛ _ _ => subst_vars; rfl
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
