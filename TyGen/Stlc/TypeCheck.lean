import Aesop

import Stlc.Bound
import Stlc.Statics

namespace Statics.Expr

def erase {Γ : Context} {τ : Ty} : (Γ ⊢ τ) → Bound.Expr Γ.length
  | .var a => Bound.Expr.var a.to_fin
  | .triv => Bound.Expr.triv
  | .pair e₁ e₂ => Bound.Expr.pair (erase e₁) (erase e₂)
  | .projₗ e => Bound.Expr.projₗ (erase e)
  | .projᵣ e => Bound.Expr.projᵣ (erase e)
  | @Expr.nullary_case _ τ e => Bound.Expr.nullary_case τ e.erase
  | @Expr.inₗ _ τₗ τᵣ e => Bound.Expr.inₗ τₗ τᵣ e.erase
  | @Expr.inᵣ _ τₗ τᵣ e => Bound.Expr.inᵣ τₗ τᵣ e.erase
  | .binary_case e eₗ eᵣ => Bound.Expr.binary_case e.erase eₗ.erase eᵣ.erase
  | @Expr.generic_ext _ ρ _ _ _ τ_op _ _ e₁ e₂ => Bound.Expr.generic_ext τ_op ρ e₁.erase e₂.erase
  | @Expr.abstraction _ τ _ e => Bound.Expr.abstraction τ e.erase
  | .application e₁ e₂ => Bound.Expr.application e₁.erase e₂.erase

mutual

def infer (Γ : Context) : (e : Bound.Expr Γ.length) → Option (Σ τ : Ty, Γ ⊢ τ)
  | .var i =>
      let ⟨a⟩ := VarIn.from_fin Γ i
      some ⟨_, Expr.var a⟩
  | .triv => some ⟨_, Expr.triv⟩
  | .pair e₁ e₂ => do
      let ⟨τ₁, e₁'⟩ ← infer Γ e₁
      let ⟨τ₂, e₂'⟩ ← infer Γ e₂
      some ⟨_, Expr.pair e₁' e₂'⟩
  | .projₗ e => do
      let ⟨τ', e'⟩ ← infer Γ e

      match τ' with
      | .prod _ _ => some ⟨_, Expr.projₗ e'⟩
      | _ => none
  | .projᵣ e => do
      let ⟨τ', e'⟩ ← infer Γ e

      match τ' with
      | .prod _ _ => some ⟨_, Expr.projᵣ e'⟩
      | _ => none
  | .nullary_case τ e => do
      let e' ← check Γ e Ty.void
      some ⟨_, @Expr.nullary_case _ τ e'⟩
  | .inₗ τₗ τᵣ e => do
      let e' ← check Γ e τₗ
      some ⟨_, @Expr.inₗ _ τₗ τᵣ e'⟩
  | .inᵣ τₗ τᵣ e => do
      let e' ← check Γ e τᵣ
      some ⟨_, @Expr.inᵣ _ τₗ τᵣ e'⟩
  | .binary_case e eₗ eᵣ => do
      let ⟨τ, e'⟩ ← infer Γ e

      match τ with
      | .sum τₗ τᵣ =>
          let ⟨τₗ', eₗ'⟩ ← infer (τₗ :: Γ) eₗ
          let ⟨τᵣ', eᵣ'⟩ ← infer (τᵣ :: Γ) eᵣ

          match decEq τₗ' τᵣ' with
          | isTrue _ => by subst_vars; exact some ⟨_, Expr.binary_case e' eₗ' eᵣ'⟩
          | isFalse _ => none
      | _ => none
  | .generic_ext τ_op ρ e₁ e₂ => do
      let ⟨ρ', e₁'⟩ ← infer (ρ :: Γ) e₁
      let ⟨τ_in, s₁⟩ := τ_op.infer ρ
      let ⟨_, s₂⟩ := τ_op.infer ρ'
      let e₂' ← check Γ e₂ τ_in
      some ⟨_, Expr.generic_ext τ_op s₁ s₂ e₁' e₂'⟩
  | .abstraction τ e => do
      let ⟨τ', e'⟩ ← infer (τ :: Γ) e
      some ⟨_, Expr.abstraction e'⟩
  | .application e₁ e₂ => do
      let ⟨τ, e₁'⟩ ← infer Γ e₁

      match τ with
      | .arrow τ τ' =>
          let e₂' ← check Γ e₂ τ
          some ⟨_, Expr.application e₁' e₂'⟩
      | _ => none

def check (Γ : Context) : (e : Bound.Expr Γ.length) → (τ : Ty) → Option (Γ ⊢ τ)
  | .var i, τ =>
      let { τ := τ', a } := VarIn.from_fin Γ i
      match decEq τ τ' with
      | isTrue eq => some (by subst_vars; exact Expr.var a)
      | isFalse _ => none
  | .triv, Ty.unit => some Expr.triv
  | .triv, _ => none
  | .pair e₁ e₂, Ty.prod τ₁ τ₂ => do
      let e₁' ← check Γ e₁ τ₁
      let e₂' ← check Γ e₂ τ₂
      some (Expr.pair e₁' e₂')
  | .pair _ _, _ => none
  | .projₗ e, τ => do
      let ⟨τ', e'⟩ ← infer Γ e

      match τ' with
      | .prod τ₁ _ =>
          match decEq τ τ₁ with
          | isTrue eq => by subst_vars; exact some (Expr.projₗ e')
          | isFalse _ => none
      | _ => none
  | .projᵣ e, τ => do
      let ⟨τ', e'⟩ ← infer Γ e

      match τ' with
      | .prod _ τ₂ =>
          match decEq τ τ₂ with
          | isTrue eq => by subst_vars; exact some (Expr.projᵣ e')
          | isFalse _ => none
      | _ => none
  | @Bound.Expr.nullary_case _ τ e, τ' => do
      let e' ← check Γ e Ty.void
      match decEq τ τ' with
      | isTrue _ => some (Expr.nullary_case e')
      | isFalse _ => none
  | @Bound.Expr.inₗ _ τₗ τᵣ e, Ty.sum τₗ' τᵣ' => do
      let e' ← check Γ e τₗ
      match decEq τₗ τₗ', decEq τᵣ τᵣ' with
      | isTrue _, isTrue _ => by subst_vars; exact some (@Expr.inₗ _ τₗ' τᵣ' e')
      | _, _ => none
  | .inₗ _ _ _, _  => none
  | @Bound.Expr.inᵣ _ τₗ τᵣ e, Ty.sum τₗ' τᵣ' => do
      let e' ← check Γ e τᵣ
      match decEq τₗ τₗ', decEq τᵣ τᵣ' with
      | isTrue _, isTrue _ => by subst_vars; exact some (@Expr.inᵣ _ τₗ' τᵣ' e')
      | _, _ => none
  | .inᵣ _ _ _, _  => none
  | .binary_case e eₗ eᵣ, τ' => do
      let ⟨τ, e'⟩ ← infer Γ e

      match τ with
      | .sum τₗ τᵣ =>
          let ⟨τₗ', eₗ'⟩ ← infer (τₗ :: Γ) eₗ
          let ⟨τᵣ', eᵣ'⟩ ← infer (τᵣ :: Γ) eᵣ

          match decEq τₗ' τᵣ', decEq τᵣ' τ' with
          | isTrue _, isTrue _  => by subst_vars; exact some (Expr.binary_case e' eₗ' eᵣ')
          | _, _ => none
      | _ => none
  | .generic_ext τ_op ρ e₁ e₂, τ => do
      let ⟨ρ', e₁'⟩ ← infer (ρ :: Γ) e₁
      let ⟨τ_in, s₁⟩ := τ_op.infer ρ
      let ⟨τ_out, s₂⟩ := τ_op.infer ρ'
      let e₂' ← check Γ e₂ τ_in

      match decEq τ τ_out with
      | isTrue _ => by subst_vars; exact some (Expr.generic_ext τ_op s₁ s₂ e₁' e₂')
      | isFalse _ => none
  | .abstraction τ₁ e, Ty.arrow τ₁' τ₂ =>
      match decEq τ₁ τ₁' with
      | isTrue eq => do
          let e' ← check (τ₁' :: Γ) e τ₂
          some (by subst_vars; exact Expr.abstraction e')
      | isFalse _ => none
  | .abstraction _ _, _ => none
  | .application e₁ e₂, τ' => do
      let ⟨τ, e₂'⟩ ← infer Γ e₂
      let e₁' ← check Γ e₁ (Ty.arrow τ τ')
      some (Expr.application e₁' e₂')

end

mutual

def infer_sound {Γ : Context} {τ : Ty} : (e : Γ ⊢ τ) → infer Γ e.erase = some ⟨τ, e⟩
  | .var a => by simp only [erase, infer]; rw [VarIn.to_from_fin_inverse]
  | .triv => by simp only [erase, infer]
  | .pair e₁ e₂ => by simp only [erase, infer, infer_sound e₁, infer_sound e₂, Bind.bind, Option.bind]
  | .projₗ e => by simp only [erase, infer, infer_sound e, Bind.bind, Option.bind]
  | .projᵣ e => by simp only [erase, infer, infer_sound e, Bind.bind, Option.bind]
  | .nullary_case e => by simp only [erase, infer, check_sound e, Bind.bind, Option.bind]
  | .inₗ e => by simp only [erase, infer, check_sound e, Bind.bind, Option.bind]
  | .inᵣ e => by simp only [erase, infer, check_sound e, Bind.bind, Option.bind]
  | .binary_case e eₗ eᵣ => by simp only [infer_sound e, infer_sound eₗ, infer_sound eᵣ, erase, infer, Bind.bind, Option.bind]; aesop
  | .generic_ext τ_op s₁ s₂ e₁ e₂ => by
        simp only [infer, erase, infer_sound e₁, Bind.bind, Option.bind]
        rw [TyOperator.infer_sound s₁, TyOperator.infer_sound s₂]
        simp only [check_sound e₂]
  | .abstraction e => by simp only [erase, infer, infer_sound e, Bind.bind, Option.bind]
  | .application e₁ e₂ => by simp only [erase, infer, infer_sound e₁, check_sound e₂, Bind.bind, Option.bind]

def check_sound {Γ : Context} {τ : Ty} : (t : Γ ⊢ τ) → check Γ t.erase τ = some t
  | .var a => by
      simp only [erase, check]
      rw [VarIn.to_from_fin_inverse]
      cases decEq τ τ with
      | isTrue => rfl
      | isFalse => contradiction
  | .triv => by simp only [erase, check]
  | .pair e₁ e₂ => by simp only [erase, check, check_sound e₁, check_sound e₂, Bind.bind, Option.bind]
  | .projₗ e => by
      simp only [erase, check, infer_sound e, Bind.bind, Option.bind]
      match decEq τ τ with
      | isTrue _ => simp only
      | isFalse _ => contradiction
  | .projᵣ e => by
      simp only [erase, check, infer_sound e, Bind.bind, Option.bind]
      match decEq τ τ with
      | isTrue _ => simp only
      | isFalse _ => contradiction
  | .nullary_case e => by simp only [erase, check, check_sound e, Bind.bind, Option.bind]; aesop
  | @Expr.inₗ _ τₗ τᵣ e => by
      simp only [erase, check, check_sound e, Bind.bind, Option.bind]
      match decEq τₗ τₗ, decEq τᵣ τᵣ with
      | isTrue _, isTrue _  => rfl
      | isFalse _, _ => contradiction
  | @Expr.inᵣ _ τₗ τᵣ e => by
      simp only [erase, check, check_sound e, Bind.bind, Option.bind]
      match decEq τₗ τₗ, decEq τᵣ τᵣ with
      | isTrue _, isTrue _  => rfl
      | isFalse _, _ => contradiction
  | .binary_case e eₗ eᵣ => by
      simp only [erase, check, infer_sound e, infer_sound eₗ, infer_sound eᵣ, Bind.bind, Option.bind]
      match decEq τ τ with
      | isTrue _ => rfl
      | isFalse _ => contradiction
  | .generic_ext τ_op s₁ s₂ e₁ e₂ => by
      simp only [erase, check, infer_sound e₁, Bind.bind, Option.bind]
      rw [TyOperator.infer_sound s₁, TyOperator.infer_sound s₂]
      simp only [check_sound e₂]
      match decEq τ τ with
      | isTrue _ => rfl
      | isFalse _ => contradiction
  | @Expr.abstraction _ τ τ' e => by
      simp only [erase, check]
      match decEq τ τ with
      | isTrue _ => simp only [check_sound e, Bind.bind, Option.bind]
      | isFalse _ => contradiction
  | .application e₁ e₂ => by simp only [erase, check, infer_sound e₂, check_sound e₁, Bind.bind, Option.bind]

end

mutual

def infer_complete
  {Γ : Context} {e : Bound.Expr Γ.length} {τ : Ty}
  (h : infer Γ e = none) :
  (Σ' e' : Γ ⊢ τ, e'.erase = e) → Empty :=
by
  intro ⟨e, eq⟩
  match e with
  | .var a | .triv => unfold erase infer at *; subst_vars; contradiction
  | .pair e₁ e₂ =>
      unfold erase infer at *
      subst_vars
      simp only [infer_sound e₁, infer_sound e₂, Bind.bind, Option.bind] at h
  | .projₗ e =>
      unfold erase infer at *
      subst_vars
      simp only [infer_sound e, Bind.bind, Option.bind] at h
  | .projᵣ e =>
      unfold erase infer at *
      subst_vars
      simp only [infer_sound e, Bind.bind, Option.bind] at h
  | .nullary_case e =>
      unfold erase infer at *
      subst_vars
      simp only [check_sound e, Bind.bind, Option.bind] at h
  | .inₗ e =>
      unfold erase infer at *
      subst_vars
      simp only [check_sound e, Bind.bind, Option.bind] at h
  | .inᵣ e =>
      unfold erase infer at *
      subst_vars
      simp only [check_sound e, Bind.bind, Option.bind] at h
  | .binary_case e eₗ eᵣ =>
      unfold erase infer at *
      subst_vars
      simp only [infer_sound e, infer_sound eₗ, infer_sound eᵣ, Bind.bind, Option.bind] at h
      match g : decEq τ τ with
      | isTrue _ => rw [g] at h; simp_all
      | isFalse _ => contradiction
  | .generic_ext τ_op s₁ s₂ e₁ e₂ =>
      unfold erase infer at *
      subst_vars
      simp only [infer_sound e₁, Bind.bind, Option.bind] at h
      rw [TyOperator.infer_sound s₁, TyOperator.infer_sound s₂] at h
      simp only [check_sound e₂] at h
  | .abstraction e =>
      unfold erase infer at *
      subst_vars
      simp only [infer_sound e, Bind.bind, Option.bind] at h
  | .application e₁ e₂ =>
      unfold erase infer at *
      subst_vars
      simp only [infer_sound e₁, check_sound e₂, Bind.bind, Option.bind] at h

def check_complete
  {Γ : Context} {e : Bound.Expr Γ.length} {τ : Ty}
  (h : check Γ e τ = none) :
  (Σ' e' : Γ ⊢ τ, e'.erase = e) → Empty :=
by
  intro ⟨e, eq⟩
  match e with
  | .var a =>
      unfold erase check at *
      subst eq
      simp at h
      rw [VarIn.to_from_fin_inverse] at h
      match h' : decEq τ τ with
      | isTrue _ => subst_vars; simp_all only
      | isFalse _ => contradiction
  | .triv => unfold erase check at *; subst eq; contradiction
  | .pair e₁ e₂ =>
      unfold erase check at *
      subst_vars
      simp only [check_sound e₁, check_sound e₂, Bind.bind, Option.bind] at h
  | .projₗ e =>
      unfold erase check at *
      subst_vars
      simp only [infer_sound e, Bind.bind, Option.bind] at h
      match h' : decEq τ τ with
      | isTrue _ => simp_all only
      | isFalse _ => contradiction
  | .projᵣ e =>
      unfold erase check at *
      subst_vars
      simp only [infer_sound e, Bind.bind, Option.bind] at h
      match h' : decEq τ τ with
      | isTrue _ => simp_all only
      | isFalse _ => contradiction
  | .nullary_case e =>
      unfold erase check at *
      subst_vars
      simp only [check_sound e, Bind.bind, Option.bind] at h
      match g : decEq τ τ with
      | isTrue _ => rw [g] at h; simp_all
      | isFalse _ => contradiction
  | @Expr.inₗ _ τₗ τᵣ e =>
      unfold erase check at *
      subst_vars
      simp only [check_sound e, Bind.bind, Option.bind] at h
      match gₗ : decEq τₗ τₗ, gᵣ : decEq τᵣ τᵣ with
      | isTrue _, isTrue _ => rw [gₗ, gᵣ] at h; simp_all
      | isFalse _, _ => contradiction
  | @Expr.inᵣ _ τₗ τᵣ e =>
      unfold erase check at *
      subst_vars
      simp only [check_sound e, Bind.bind, Option.bind] at h
      match gₗ : decEq τₗ τₗ, gᵣ : decEq τᵣ τᵣ with
      | isTrue _, isTrue _ => rw [gₗ, gᵣ] at h; simp_all
      | isFalse _, _ => contradiction
  | .binary_case e eₗ eᵣ =>
      unfold erase check at *
      subst_vars
      simp only [infer_sound e, infer_sound eₗ, infer_sound eᵣ, Bind.bind, Option.bind] at h
      match g : decEq τ τ with
      | isTrue _ => rw [g] at h; simp_all
      | isFalse _ => contradiction
  | .generic_ext τ_op s₁ s₂ e₁ e₂ =>
      unfold erase check at *
      subst_vars
      simp only [infer_sound e₁, Bind.bind, Option.bind] at h
      rw [TyOperator.infer_sound s₁, TyOperator.infer_sound s₂] at h
      simp only [check_sound e₂] at h
      match g : decEq τ τ with
      | isTrue _ => rw [g] at h; simp_all
      | isFalse _ => contradiction
  | @Expr.abstraction _ τ _ e =>
      unfold erase check at *
      subst_vars
      simp only at h
      match h' : decEq τ τ with
      | isTrue _ => subst_vars; simp_all only [check_sound e, Bind.bind, Option.bind]
      | isFalse _ => contradiction
  | .application e₁ e₂ =>
      unfold erase check at *
      subst_vars
      simp only [check_sound e₁, infer_sound e₂, Bind.bind, Option.bind] at h

end
