import Stlc.Dynamics.Normal
import Stlc.Statics

open Statics

namespace Dynamics

inductive Transition {Γ : Context} : {τ : Ty} → (Γ ⊢ τ) → (Γ ⊢ τ) → Type where
  | ξ_pairₗ
      {τₗ τᵣ : Ty} {eₗ eₗ' : Γ ⊢ τₗ} {eᵣ : Γ ⊢ τᵣ} :
      Transition eₗ eₗ' →
      Transition (Expr.pair eₗ eᵣ) (Expr.pair eₗ' eᵣ)

  | ξ_pairᵣ
      {τₗ τᵣ : Ty} {eₗ : Γ ⊢ τₗ} {eᵣ eᵣ' : Γ ⊢ τᵣ} :
      Normal eₗ →
      Transition eᵣ eᵣ' →
      Transition (Expr.pair eₗ eᵣ) (Expr.pair eₗ eᵣ')

  | ξ_projₗ
      {τₗ τᵣ : Ty} {e e' : Γ ⊢ Ty.prod τₗ τᵣ} :
      Transition e e' →
      Transition (Expr.projₗ e) (Expr.projₗ e')

  | β_projₗ
      {τₗ τᵣ : Ty} {eₗ : Γ ⊢ τₗ} {eᵣ : Γ ⊢ τᵣ} :
      Value eₗ →
      Value eᵣ →
      Transition (Expr.projₗ (Expr.pair eₗ eᵣ)) eₗ

  | ξ_projᵣ
      {τₗ τᵣ : Ty} {e e' : Γ ⊢ Ty.prod τₗ τᵣ} :
      Transition e e' →
      Transition (Expr.projᵣ e) (Expr.projᵣ e')

  | β_projᵣ
      {τₗ τᵣ : Ty} {eₗ : Γ ⊢ τₗ} {eᵣ : Γ ⊢ τᵣ} :
      Value eₗ →
      Value eᵣ →
      Transition (Expr.projᵣ (Expr.pair eₗ eᵣ)) eᵣ

  | ξ_nullary_case
      {e e' : Γ ⊢ Ty.void} :
      Transition e e' →
      Transition (Expr.nullary_case e) (Expr.nullary_case e')

  | ξ_inₗ
      {τₗ τᵣ : Ty} {eₗ eₗ' : Γ ⊢ τₗ} :
      Transition eₗ eₗ' →
      Transition (@Expr.inₗ Γ τₗ τᵣ eₗ) (Expr.inₗ eₗ')

  | ξ_inᵣ
      {τₗ τᵣ : Ty} {eᵣ eᵣ' : Γ ⊢ τᵣ} :
      Transition eᵣ eᵣ' →
      Transition (@Expr.inᵣ Γ τₗ τᵣ eᵣ) (Expr.inᵣ eᵣ')

  | ξ_binary_case
      {τ τₗ τᵣ : Ty} {e e' : Γ ⊢ Ty.sum τₗ τᵣ} {eₗ : (τₗ :: Γ) ⊢ τ} {eᵣ : (τᵣ :: Γ) ⊢ τ} :
      Transition e e' →
      Transition (Expr.binary_case e eₗ eᵣ) (Expr.binary_case e' eₗ eᵣ)

  | β_binary_caseₗ
      {τ τₗ τᵣ : Ty} {e : Γ ⊢ τₗ} {e' : Γ ⊢ τ} {eₗ : (τₗ :: Γ) ⊢ τ} {eᵣ : (τᵣ :: Γ) ⊢ τ} :
      e' = eₗ [ e ] →
      Value e →
      Transition (Expr.binary_case (Expr.inₗ e) eₗ eᵣ) e'

  | β_binary_caseᵣ
      {τ τₗ τᵣ : Ty} {e : Γ ⊢ τᵣ} {e' : Γ ⊢ τ} {eₗ : (τₗ :: Γ) ⊢ τ} {eᵣ : (τᵣ :: Γ) ⊢ τ} :
      e' = eᵣ [ e ] →
      Value e →
      Transition (Expr.binary_case (Expr.inᵣ e) eₗ eᵣ) e'

  | β_generic_ext_var
      {ρ ρ' : Ty} {e_out : Γ ⊢ ρ'}
      (e' : (ρ :: Γ) ⊢ ρ') (e : Γ ⊢ ρ) :
      e_out = e' [ e ] →
      Transition (Expr.generic_ext TyOperator.var TyOperator.Subst.var TyOperator.Subst.var e' e) e_out

  | β_generic_ext_unit
      {ρ ρ' : Ty}
      (e' : (ρ :: Γ) ⊢ ρ') (e : Γ ⊢ Ty.unit) :
      Transition (Expr.generic_ext TyOperator.unit TyOperator.Subst.unit TyOperator.Subst.unit e' e) e

  | β_generic_ext_prod
      {ρ ρ' τ_inₗ τ_inᵣ τ_outₗ τ_outᵣ : Ty} {τ_opₗ τ_opᵣ : TyOperator}
      (sₗ : TyOperator.Subst ρ τ_opₗ τ_inₗ) (sₗ' : TyOperator.Subst ρ' τ_opₗ τ_outₗ)
      (sᵣ : TyOperator.Subst ρ τ_opᵣ τ_inᵣ) (sᵣ' : TyOperator.Subst ρ' τ_opᵣ τ_outᵣ)
      (e' : (ρ :: Γ) ⊢ ρ') (e : Γ ⊢ Ty.prod τ_inₗ τ_inᵣ) :
      Transition (Expr.generic_ext (TyOperator.prod τ_opₗ τ_opᵣ) (TyOperator.Subst.prod sₗ sᵣ) (TyOperator.Subst.prod sₗ' sᵣ') e' e)
                 (Expr.pair (Expr.generic_ext τ_opₗ sₗ sₗ' e' (Expr.projₗ e)) (Expr.generic_ext τ_opᵣ sᵣ sᵣ' e' (Expr.projᵣ e)))

  | β_generic_ext_void
      {ρ ρ' : Ty}
      (e' : (ρ :: Γ) ⊢ ρ') (e : Γ ⊢ Ty.void) :
      Transition (Expr.generic_ext TyOperator.void TyOperator.Subst.void TyOperator.Subst.void e' e) (Expr.nullary_case e)

  | β_generic_ext_sum
      {ρ ρ' τ_inₗ τ_inᵣ τ_outₗ τ_outᵣ : Ty} {τ_opₗ τ_opᵣ : TyOperator}
      {e'_outₗ : ρ :: τ_inₗ :: Γ ⊢ ρ'} {e'_outᵣ : ρ :: τ_inᵣ :: Γ ⊢ ρ'}
      (sₗ : TyOperator.Subst ρ τ_opₗ τ_inₗ) (sₗ' : TyOperator.Subst ρ' τ_opₗ τ_outₗ)
      (sᵣ : TyOperator.Subst ρ τ_opᵣ τ_inᵣ) (sᵣ' : TyOperator.Subst ρ' τ_opᵣ τ_outᵣ)
      (e' : (ρ :: Γ) ⊢ ρ') (e : Γ ⊢ Ty.sum τ_inₗ τ_inᵣ) :
      e'_outₗ = ((⟪ ↑ ⟫) e').swap →
      e'_outᵣ = ((⟪ ↑ ⟫) e').swap →
      Transition (Expr.generic_ext (TyOperator.sum τ_opₗ τ_opᵣ) (TyOperator.Subst.sum sₗ sᵣ) (TyOperator.Subst.sum sₗ' sᵣ') e' e)
                 (Expr.binary_case e
                                   (Expr.inₗ (Expr.generic_ext τ_opₗ sₗ sₗ' e'_outₗ (Expr.var VarIn.here)))
                                   (Expr.inᵣ (Expr.generic_ext τ_opᵣ sᵣ sᵣ' e'_outᵣ (Expr.var VarIn.here))))

  | β_generic_ext_arrow
      {ρ ρ' τ_in₁ τ_in₂ τ_out₂ : Ty} {τ_op₂ : TyOperator}
      {e_out : τ_in₁ :: Γ ⊢ Ty.arrow τ_in₁ τ_in₂} {e'_out : ρ :: τ_in₁ :: Γ ⊢ ρ'}
      (s : TyOperator.Subst ρ τ_op₂ τ_in₂) (s' : TyOperator.Subst ρ' τ_op₂ τ_out₂)
      (e' : (ρ :: Γ) ⊢ ρ') (e : Γ ⊢ Ty.arrow τ_in₁ τ_in₂) :
      e_out = (⟪ ↑ ⟫) e →
      e'_out = ((⟪ ↑ ⟫) e').swap →
      Transition (Expr.generic_ext (TyOperator.arrow τ_in₁ τ_op₂) (TyOperator.Subst.arrow s) (TyOperator.Subst.arrow s') e' e)
                 (Expr.abstraction (Expr.generic_ext τ_op₂ s s' e'_out (Expr.application e_out (Expr.var VarIn.here))))

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

def ξ_pairₗ
  {Γ : Context} {τₗ τᵣ : Ty} {eₗ eₗ' : Γ ⊢ τₗ} {eᵣ : Γ ⊢ τᵣ} :
  (eₗ ⟶* eₗ') →
  (Expr.pair eₗ eᵣ ⟶* Expr.pair eₗ' eᵣ)
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr mtr =>
      calc
        _ ⟶ (Expr.pair _ _) := Transition.ξ_pairₗ tr
        _ ⟶* _ := ξ_pairₗ mtr

def ξ_pairᵣ
  {Γ : Context} {τₗ τᵣ : Ty} {eₗ : Γ ⊢ τₗ} {eᵣ eᵣ' : Γ ⊢ τᵣ}
  (normₗ : Normal eₗ) :
  (eᵣ ⟶* eᵣ') →
  (Expr.pair eₗ eᵣ ⟶* Expr.pair eₗ eᵣ')
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr mtr =>
      calc
        _ ⟶ (Expr.pair _ _) := Transition.ξ_pairᵣ normₗ tr
        _ ⟶* _ := ξ_pairᵣ normₗ mtr

def ξ_projₗ
  {Γ : Context} {τₗ τᵣ : Ty} {e e' : Γ ⊢ Ty.prod τₗ τᵣ} :
  (e ⟶* e') →
  (Expr.projₗ e ⟶* Expr.projₗ e')
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr mtr =>
      calc
        _ ⟶ (Expr.projₗ _) := Transition.ξ_projₗ tr
        _ ⟶* _ := ξ_projₗ mtr

def ξ_projᵣ
  {Γ : Context} {τₗ τᵣ : Ty} {e e' : Γ ⊢ Ty.prod τₗ τᵣ} :
  (e ⟶* e') →
  (Expr.projᵣ e ⟶* Expr.projᵣ e')
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr mtr =>
      calc
        _ ⟶ (Expr.projᵣ _) := Transition.ξ_projᵣ tr
        _ ⟶* _ := ξ_projᵣ mtr

def ξ_nullary_case
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ Ty.void} :
  (e ⟶* e') →
  (@Expr.nullary_case Γ τ e ⟶* Expr.nullary_case e')
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr mtr =>
      calc
        _ ⟶ (Expr.nullary_case _) := Transition.ξ_nullary_case tr
        _ ⟶* _ := ξ_nullary_case mtr

def ξ_inₗ
  {Γ : Context} {τₗ τᵣ : Ty} {eₗ eₗ' : Γ ⊢ τₗ} :
  (eₗ ⟶* eₗ') →
  (@Expr.inₗ Γ τₗ τᵣ eₗ ⟶* Expr.inₗ eₗ')
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr mtr =>
      calc
        _ ⟶ (Expr.inₗ _) := Transition.ξ_inₗ tr
        _ ⟶* _ := ξ_inₗ mtr

def ξ_inₗ_inv
  {Γ : Context} {τₗ τᵣ : Ty} {eₗ eₗ' : Γ ⊢ τₗ} :
  (@Expr.inₗ Γ τₗ τᵣ eₗ ⟶* Expr.inₗ eₗ') →
  (eₗ ⟶* eₗ')
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr mtr =>
      match tr with
      | .ξ_inₗ tr =>
          calc
              _ ⟶ _ := tr
              _ ⟶* _ := ξ_inₗ_inv mtr

def ξ_inᵣ
  {Γ : Context} {τₗ τᵣ : Ty} {eᵣ eᵣ' : Γ ⊢ τᵣ} :
  (eᵣ ⟶* eᵣ') →
  (@Expr.inᵣ Γ τₗ τᵣ eᵣ ⟶* Expr.inᵣ eᵣ')
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr mtr =>
      calc
        _ ⟶ (Expr.inᵣ _) := Transition.ξ_inᵣ tr
        _ ⟶* _ := ξ_inᵣ mtr

def ξ_inᵣ_inv
  {Γ : Context} {τₗ τᵣ : Ty} {eᵣ eᵣ' : Γ ⊢ τᵣ} :
  (@Expr.inᵣ Γ τₗ τᵣ eᵣ ⟶* Expr.inᵣ eᵣ') →
  (eᵣ ⟶* eᵣ')
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr mtr =>
      match tr with
      | .ξ_inᵣ tr =>
          calc
              _ ⟶ _ := tr
              _ ⟶* _ := ξ_inᵣ_inv mtr

def ξ_binary_case
  {Γ : Context} {τ τₗ τᵣ : Ty} {e e' : Γ ⊢ Ty.sum τₗ τᵣ} {eₗ : (τₗ :: Γ) ⊢ τ} {eᵣ : (τᵣ :: Γ) ⊢ τ} :
  (e ⟶* e') →
  (Expr.binary_case e eₗ eᵣ ⟶* Expr.binary_case e' eₗ eᵣ)
  | .refl _ => Transitionᵣₜ.refl _
  | .trans _ tr mtr =>
      calc
        _ ⟶ (Expr.binary_case _ _ _) := Transition.ξ_binary_case tr
        _ ⟶* _ := ξ_binary_case mtr

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
  | .pair eₗ eᵣ =>
      match eₗ.normal_or_reduces, eᵣ.normal_or_reduces with
      | .inl (.value valₗ), .inl (.value valᵣ) => Sum.inl (Value.pair valₗ valᵣ).normal
      | .inl (.neutral neutₗ), .inl normᵣ => Sum.inl (Neutral.pairₗ neutₗ normᵣ).normal
      | .inl (.value valₗ), .inl (.neutral neutᵣ) => Sum.inl (Neutral.pairᵣ valₗ neutᵣ).normal
      | .inr ⟨_, trₗ⟩, _ => Sum.inr ⟨_, Transition.ξ_pairₗ trₗ⟩
      | .inl normₗ, .inr ⟨_, trᵣ⟩ => Sum.inr ⟨_, Transition.ξ_pairᵣ normₗ trᵣ⟩
  | .projₗ e =>
      match e.normal_or_reduces with
      | .inl (.value (Value.pair valₗ valᵣ)) => Sum.inr ⟨_, Transition.β_projₗ valₗ valᵣ⟩
      | .inl (.neutral neut) => Sum.inl (Neutral.projₗ neut).normal
      | .inr ⟨_, tr⟩ => Sum.inr ⟨_, Transition.ξ_projₗ tr⟩
  | .projᵣ e =>
      match e.normal_or_reduces with
      | .inl (.value (Value.pair valₗ valᵣ)) => Sum.inr ⟨_, Transition.β_projᵣ valₗ valᵣ⟩
      | .inl (.neutral neut) => Sum.inl (Neutral.projᵣ neut).normal
      | .inr ⟨_, tr⟩ => Sum.inr ⟨_, Transition.ξ_projᵣ tr⟩
  | .nullary_case e =>
      match e.normal_or_reduces with
      | .inl (.neutral neut) => Sum.inl (Neutral.nullary_case neut).normal
      | .inr ⟨_, tr⟩ => Sum.inr ⟨_, Transition.ξ_nullary_case tr⟩
  | .inₗ eₗ =>
      match eₗ.normal_or_reduces with
      | .inl (.value valₗ) => Sum.inl (Value.inₗ valₗ).normal
      | .inl (.neutral neutₗ) => Sum.inl (Neutral.inₗ neutₗ).normal
      | .inr ⟨_, tr⟩ => Sum.inr ⟨_, Transition.ξ_inₗ tr⟩
  | .inᵣ eᵣ =>
      match eᵣ.normal_or_reduces with
      | .inl (.value valᵣ) => Sum.inl (Value.inᵣ valᵣ).normal
      | .inl (.neutral neutᵣ) => Sum.inl (Neutral.inᵣ neutᵣ).normal
      | .inr ⟨_, tr⟩ => Sum.inr ⟨_, Transition.ξ_inᵣ tr⟩
  | .binary_case e _ _ =>
      match e.normal_or_reduces with
      | .inl (.value (.inₗ val)) => Sum.inr ⟨_, Transition.β_binary_caseₗ rfl val⟩
      | .inl (.value (.inᵣ val)) => Sum.inr ⟨_, Transition.β_binary_caseᵣ rfl val⟩
      | .inl (.neutral neut) => Sum.inl (Neutral.binary_case neut).normal
      | .inr ⟨_, tr⟩ => Sum.inr ⟨_, Transition.ξ_binary_case tr⟩
  | .generic_ext τ_op s s' e' e => by
      match τ_op with
      | .var =>
          cases s
          cases s'
          exact Sum.inr ⟨_, Transition.β_generic_ext_var e' e rfl⟩
      | .unit =>
          cases s
          cases s'
          exact Sum.inr ⟨_, Transition.β_generic_ext_unit e' e⟩
      | .prod τ_opₗ τ_opᵣ =>
          cases s
          cases s'
          rename_i sₗ sᵣ _ _ sₗ' sᵣ'
          exact Sum.inr ⟨_, Transition.β_generic_ext_prod sₗ sₗ' sᵣ sᵣ' e' e⟩
      | .void =>
          cases s
          cases s'
          exact Sum.inr ⟨_, Transition.β_generic_ext_void e' e⟩
      | .sum τ_opₗ τ_opᵣ =>
          cases s
          cases s'
          rename_i sₗ sᵣ _ _ sₗ' sᵣ'
          exact Sum.inr ⟨_, Transition.β_generic_ext_sum sₗ sₗ' sᵣ sᵣ' e' e rfl rfl⟩
      | .arrow τ₁ τ_op₂ =>
          cases s
          cases s'
          rename_i s _ s'
          exact Sum.inr ⟨_, Transition.β_generic_ext_arrow s s' e' e rfl rfl⟩
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
  | .pair valₗ _, .ξ_pairₗ trₗ => valₗ.does_not_reduce trₗ
  | .pair _ valᵣ, .ξ_pairᵣ norm₁ trᵣ => valᵣ.does_not_reduce trᵣ
  | .inₗ valₗ, .ξ_inₗ trₗ => valₗ.does_not_reduce trₗ
  | .inᵣ valᵣ, .ξ_inᵣ trᵣ => valᵣ.does_not_reduce trᵣ
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
  | .pairₗ neutₗ normᵣ => by
      cases tr with
      | ξ_pairₗ trₗ => exact neutₗ.does_not_reduce trₗ
      | ξ_pairᵣ _ trᵣ => exact normᵣ.does_not_reduce trᵣ
  | .pairᵣ valₗ neutᵣ => by
      cases tr with
      | ξ_pairₗ trₗ => exact valₗ.does_not_reduce trₗ
      | ξ_pairᵣ normₗ trᵣ => exact neutᵣ.does_not_reduce trᵣ
  | .projₗ neut => by
      cases tr with
      | ξ_projₗ tr => exact neut.does_not_reduce tr
      | β_projₗ valₗ valᵣ =>
          cases neut with
          | pairₗ neutₗ _ => exact valₗ.not_neutral neutₗ
          | pairᵣ _ neutᵣ => exact valᵣ.not_neutral neutᵣ
  | .projᵣ neut => by
      cases tr with
      | ξ_projᵣ tr => exact neut.does_not_reduce tr
      | β_projᵣ valₗ valᵣ =>
          cases neut with
          | pairₗ neutₗ _ => exact valₗ.not_neutral neutₗ
          | pairᵣ _ neutᵣ => exact valᵣ.not_neutral neutᵣ
  | .nullary_case neut =>
      match tr with
      | .ξ_nullary_case tr => neut.does_not_reduce tr
  | .inₗ neutₗ =>
      match tr with
      | .ξ_inₗ trₗ => neutₗ.does_not_reduce trₗ
  | .inᵣ neutᵣ =>
      match tr with
      | .ξ_inᵣ trᵣ => neutᵣ.does_not_reduce trᵣ
  | .binary_case neut =>
      match tr with
      | .ξ_binary_case tr => neut.does_not_reduce tr
      | .β_binary_caseₗ _ valₗ =>
          let .inₗ neutₗ := neut
          valₗ.not_neutral neutₗ
      | .β_binary_caseᵣ _ valᵣ =>
          let .inᵣ neutᵣ := neut
          valᵣ.not_neutral neutᵣ
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
  | _, _, _, .ξ_pairₗ trₗ =>
      cases tr' with
      | ξ_pairₗ trₗ' => rw [irrelevant trₗ trₗ']
      | ξ_pairᵣ normₗ' trᵣ' => exact Empty.elim (normₗ'.does_not_reduce trₗ)
  | _, _, _, .ξ_pairᵣ normₗ trᵣ =>
      cases tr' with
      | ξ_pairₗ trₗ' => exact Empty.elim (normₗ.does_not_reduce trₗ')
      | ξ_pairᵣ normₗ' trᵣ' => rw [Normal.irrelevant normₗ normₗ', irrelevant trᵣ trᵣ']
  | _, _, _, .ξ_projₗ tr =>
      cases tr' with
      | ξ_projₗ trₗ' => rw [irrelevant tr trₗ']
      | β_projₗ valₗ' valᵣ' =>
          cases tr with
          | ξ_pairₗ trₗ => exact Empty.elim (valₗ'.does_not_reduce trₗ)
  | _, _, _, .β_projₗ valₗ valᵣ =>
      cases tr' with
      | ξ_projₗ tr' =>
          cases tr' with
          | ξ_pairₗ trₗ' => exact Empty.elim (valₗ.does_not_reduce trₗ')
      | β_projₗ valₗ' valᵣ' => rw [Value.irrelevant valₗ valₗ', Value.irrelevant valᵣ valᵣ']
  | _, _, _, .ξ_projᵣ tr =>
      cases tr' with
      | ξ_projᵣ trᵣ' => rw [irrelevant tr trᵣ']
      | β_projᵣ valₗ' valᵣ' =>
          cases tr with
          | ξ_pairᵣ normₗ' trᵣ => exact Empty.elim (valᵣ'.does_not_reduce trᵣ)
  | _, _, _, .β_projᵣ valₗ valᵣ =>
      cases tr' with
      | ξ_projᵣ tr' =>
          cases tr' with
          | ξ_pairᵣ normₗ' trᵣ' => exact Empty.elim (valᵣ.does_not_reduce trᵣ')
      | β_projᵣ valₗ' valᵣ' => rw [Value.irrelevant valₗ valₗ', Value.irrelevant valᵣ valᵣ']
  | _, _, _, .ξ_nullary_case tr =>
      cases tr' with
      | ξ_nullary_case tr' => rw [irrelevant tr tr']
  | _, _, _, .ξ_inₗ trₗ =>
      cases tr' with
      | ξ_inₗ trₗ' => rw [irrelevant trₗ trₗ']
  | _, _, _, .ξ_inᵣ trᵣ =>
      cases tr' with
      | ξ_inᵣ trᵣ' => rw [irrelevant trᵣ trᵣ']
  | _, _, _, .ξ_binary_case tr =>
      cases tr' with
      | ξ_binary_case tr' => rw [irrelevant tr tr']
      | β_binary_caseₗ hₗ' valₗ' =>
          cases tr
          rename_i trₗ
          exact Empty.elim (valₗ'.does_not_reduce trₗ)
      | β_binary_caseᵣ hᵣ' valᵣ' =>
          cases tr
          rename_i trᵣ
          exact Empty.elim (valᵣ'.does_not_reduce trᵣ)
  | _, _, _, .β_binary_caseₗ h val =>
      cases tr' with
      | ξ_binary_case tr' =>
          cases tr'
          rename_i tr'
          exact Empty.elim (val.does_not_reduce tr')
      | β_binary_caseₗ h' val' => rw [Value.irrelevant val val']
  | _, _, _, .β_binary_caseᵣ h val =>
      cases tr' with
      | ξ_binary_case tr' =>
          cases tr'
          rename_i tr'
          exact Empty.elim (val.does_not_reduce tr')
      | β_binary_caseᵣ h' val' => rw [Value.irrelevant val val']
  | _, _, _, .β_generic_ext_var e' e h =>
      cases tr' with
      | β_generic_ext_var => rfl
  | _, _, _, .β_generic_ext_unit e' e =>
      cases tr' with
      | β_generic_ext_unit => rfl
  | _, _, _, .β_generic_ext_prod _ _ _ _ _ _ =>
      cases tr' with
      | β_generic_ext_prod => rfl
  | _, _, _, .β_generic_ext_void e' e =>
      cases tr' with
      | β_generic_ext_void => rfl
  | _, _, _, .β_generic_ext_sum _ _ _ _ _ _ _ _ =>
      cases tr' with
      | β_generic_ext_sum => rfl
  | _, _, _, .β_generic_ext_arrow _ _ _ _ _ _ =>
      cases tr' with
      | β_generic_ext_arrow => rfl
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

theorem deterministic
  {Γ : Context} {τ : Ty} {e₁ e₂ e₂' : Γ ⊢ τ}
  (tr : e₁ ⟶ e₂)
  (tr' : e₁ ⟶ e₂') :
  e₂ = e₂' :=
by
  match τ, e₁, e₂, tr with
  | _, _, _, .ξ_pairₗ trₗ =>
      cases tr' with
      | ξ_pairₗ trₗ' => rw [deterministic trₗ trₗ']
      | ξ_pairᵣ normₗ' trᵣ' => exact Empty.elim (normₗ'.does_not_reduce trₗ)
  | _, _, _, .ξ_pairᵣ normₗ trᵣ =>
      cases tr' with
      | ξ_pairₗ trₗ' => exact Empty.elim (normₗ.does_not_reduce trₗ')
      | ξ_pairᵣ normₗ' trᵣ' => rw [deterministic trᵣ trᵣ']
  | _, _, _, .ξ_projₗ tr =>
      cases tr' with
      | ξ_projₗ trₗ' => rw [deterministic tr trₗ']
      | β_projₗ valₗ' valᵣ' =>
          cases tr with
          | ξ_pairₗ trₗ => exact Empty.elim (valₗ'.does_not_reduce trₗ)
          | ξ_pairᵣ normₗ trᵣ => exact Empty.elim (valᵣ'.does_not_reduce trᵣ)
  | _, _, _, .β_projₗ valₗ valᵣ =>
      cases tr' with
      | ξ_projₗ tr' =>
          cases tr' with
          | ξ_pairₗ trₗ' => exact Empty.elim (valₗ.does_not_reduce trₗ')
          | ξ_pairᵣ normₗ' trᵣ' => exact Empty.elim (valᵣ.does_not_reduce trᵣ')
      | β_projₗ valₗ' valᵣ' => rfl
  | _, _, _, .ξ_projᵣ tr =>
      cases tr' with
      | ξ_projᵣ trᵣ' => rw [deterministic tr trᵣ']
      | β_projᵣ valₗ' valᵣ' =>
          cases tr with
          | ξ_pairₗ trₗ => exact Empty.elim (valₗ'.does_not_reduce trₗ)
          | ξ_pairᵣ normₗ trᵣ => exact Empty.elim (valᵣ'.does_not_reduce trᵣ)
  | _, _, _, .β_projᵣ valₗ valᵣ =>
      cases tr' with
      | ξ_projᵣ tr' =>
          cases tr' with
          | ξ_pairₗ trₗ' => exact Empty.elim (valₗ.does_not_reduce trₗ')
          | ξ_pairᵣ normₗ' trᵣ' => exact Empty.elim (valᵣ.does_not_reduce trᵣ')
      | β_projᵣ valₗ' valᵣ' => rfl
  | _, _, _, .ξ_nullary_case tr =>
      cases tr' with
      | ξ_nullary_case tr' => rw [deterministic tr tr']
  | _, _, _, .ξ_inₗ tr =>
      cases tr' with
      | ξ_inₗ tr' => rw [deterministic tr tr']
  | _, _, _, .ξ_inᵣ tr =>
      cases tr' with
      | ξ_inᵣ tr' => rw [deterministic tr tr']
  | _, _, _, .ξ_binary_case tr =>
      cases tr' with
      | ξ_binary_case tr' => rw [deterministic tr tr']
      | β_binary_caseₗ h' val' =>
          cases tr
          rename_i tr
          exact Empty.elim (val'.does_not_reduce tr)
      | β_binary_caseᵣ h' val' =>
          cases tr
          rename_i tr
          exact Empty.elim (val'.does_not_reduce tr)
  | _, _, _, .β_binary_caseₗ h val =>
      cases tr' with
      | ξ_binary_case tr' =>
          cases tr'
          rename_i tr'
          exact Empty.elim (val.does_not_reduce tr')
      | β_binary_caseₗ h' val' => subst_vars; rfl
  | _, _, _, .β_binary_caseᵣ h val =>
      cases tr' with
      | ξ_binary_case tr' =>
          cases tr'
          rename_i tr'
          exact Empty.elim (val.does_not_reduce tr')
      | β_binary_caseᵣ h' val' => subst_vars; rfl
  | _, _, _, .β_generic_ext_var e' e h =>
      cases tr' with
      | β_generic_ext_var => subst_vars; rfl
  | _, _, _, .β_generic_ext_unit e' e =>
      cases tr' with
      | β_generic_ext_unit => rfl
  | _, _, _, .β_generic_ext_prod _ _ _ _ _ _ =>
      cases tr' with
      | β_generic_ext_prod => rfl
  | _, _, _, .β_generic_ext_void e' e =>
      cases tr' with
      | β_generic_ext_void => rfl
  | _, _, _, .β_generic_ext_sum _ _ _ _ _ _ _ _ =>
      cases tr' with
      | β_generic_ext_sum => subst_vars; rfl
  | _, _, _, .β_generic_ext_arrow _ _ _ _ _ _ =>
      cases tr' with
      | β_generic_ext_arrow => subst_vars; rfl
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
