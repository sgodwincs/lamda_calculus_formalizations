import Stlc.Bound
import Stlc.Statics

namespace Statics.Expr

def erase {Γ : Context} {τ : Ty} : (Γ ⊢ τ) → Bound.Expr Γ.length
  | .var a => Bound.Expr.var a.to_fin
  | .triv => Bound.Expr.triv
  | .pair e₁ e₂ => Bound.Expr.pair (erase e₁) (erase e₂)
  | .proj₁ e => Bound.Expr.proj₁ (erase e)
  | .proj₂ e => Bound.Expr.proj₂ (erase e)
  | @Expr.abstraction _ τ _ e => Bound.Expr.abstraction τ (erase e)
  | .application e₁ e₂ => Bound.Expr.application (erase e₁) (erase e₂)

mutual

def infer (Γ : Context) : (e : Bound.Expr Γ.length) → Option (Σ τ : Ty, Γ ⊢ τ)
  | .var i =>
      let ⟨a⟩ := Any.from_fin Γ i
      some ⟨_, Expr.var a⟩
  | .triv => some ⟨_, Expr.triv⟩
  | .pair e₁ e₂ => do
      let ⟨τ₁, e₁'⟩ ← infer Γ e₁
      let ⟨τ₂, e₂'⟩ ← infer Γ e₂
      some ⟨_, Expr.pair e₁' e₂'⟩
  | .proj₁ e => do
      let ⟨τ', e'⟩ ← infer Γ e

      match τ' with
      | .prod _ _ => some ⟨_, Expr.proj₁ e'⟩
      | _ => none
  | .proj₂ e => do
      let ⟨τ', e'⟩ ← infer Γ e

      match τ' with
      | .prod _ _ => some ⟨_, Expr.proj₂ e'⟩
      | _ => none
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
      let { τ := τ', a } := Any.from_fin Γ i
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
  | .proj₁ e, τ => do
      let ⟨τ', e'⟩ ← infer Γ e

      match τ' with
      | .prod τ₁ _ =>
          match decEq τ τ₁ with
          | isTrue eq => by subst_vars; exact some (Expr.proj₁ e')
          | isFalse _ => none
      | _ => none
  | .proj₂ e, τ => do
      let ⟨τ', e'⟩ ← infer Γ e

      match τ' with
      | .prod _ τ₂ =>
          match decEq τ τ₂ with
          | isTrue eq => by subst_vars; exact some (Expr.proj₂ e')
          | isFalse _ => none
      | _ => none
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
  | .var a => by simp only [erase, infer]; rw [Any.to_from_fin_inverse]
  | .triv => by simp only [erase, infer]
  | .pair e₁ e₂ => by simp only [erase, infer, infer_sound e₁, infer_sound e₂, Bind.bind, Option.bind]
  | .proj₁ e => by simp only [erase, infer, infer_sound e, Bind.bind, Option.bind]
  | .proj₂ e => by simp only [erase, infer, infer_sound e, Bind.bind, Option.bind]
  | .abstraction e => by simp only [erase, infer, infer_sound e, Bind.bind, Option.bind]
  | .application e₁ e₂ => by simp only [erase, infer, infer_sound e₁, check_sound e₂, Bind.bind, Option.bind]

def check_sound {Γ : Context} {τ : Ty} : (t : Γ ⊢ τ) → check Γ t.erase τ = some t
  | .var a => by
      simp only [erase, check]
      rw [Any.to_from_fin_inverse]
      cases decEq τ τ with
      | isTrue => rfl
      | isFalse => contradiction
  | .triv => by simp only [erase, check]
  | .pair e₁ e₂ => by simp only [erase, check, check_sound e₁, check_sound e₂, Bind.bind, Option.bind]
  | .proj₁ e => by
      simp only [erase, check, infer_sound e, Bind.bind, Option.bind]
      match decEq τ τ with 
      | isTrue _ => simp only
      | isFalse _ => contradiction
  | .proj₂ e => by
      simp only [erase, check, infer_sound e, Bind.bind, Option.bind]
      match decEq τ τ with
      | isTrue _ => simp only
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
  | .proj₁ e =>
      unfold erase infer at *
      subst_vars
      simp only [infer_sound e, Bind.bind, Option.bind] at h
  | .proj₂ e =>
      unfold erase infer at *
      subst_vars
      simp only [infer_sound e, Bind.bind, Option.bind] at h
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
      rw [Any.to_from_fin_inverse] at h
      match h' : decEq τ τ with
      | isTrue _ => subst_vars; simp_all only
      | isFalse _ => contradiction
  | .triv => unfold erase check at *; subst eq; contradiction
  | .pair e₁ e₂ =>
      unfold erase check at *
      subst_vars
      simp only [check_sound e₁, check_sound e₂, Bind.bind, Option.bind] at h
  | .proj₁ e =>
      unfold erase check at *
      subst_vars
      simp only [infer_sound e, Bind.bind, Option.bind] at h
      match h' : decEq τ τ with
      | isTrue _ => simp_all only
      | isFalse _ => contradiction
  | .proj₂ e =>
      unfold erase check at *
      subst_vars
      simp only [infer_sound e, Bind.bind, Option.bind] at h
      match h' : decEq τ τ with
      | isTrue _ => simp_all only
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
