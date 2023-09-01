import Stlc.Bound
import Stlc.Statics

namespace Statics.Expr

def erase {Γ : Context} {τ : Ty} : (Γ ⊢ τ) → Bound.Expr Γ.length
  | .var a => Bound.Expr.var a.to_fin
  | .number num => Bound.Expr.number num
  | .string s => Bound.Expr.string s
  | @Expr.abstraction _ τ _ e => Bound.Expr.abstraction τ (erase e)
  | .application e₁ e₂ => Bound.Expr.application (erase e₁) (erase e₂)

mutual

def infer (Γ : Context) : (e : Bound.Expr Γ.length) → Option (Σ τ : Ty, Γ ⊢ τ)
  | .var i =>
      let ⟨a⟩ := Any.from_fin Γ i
      some ⟨_, Expr.var a⟩
  | .number num => some ⟨_, Expr.number num⟩
  | .string s => some ⟨_, Expr.string s⟩
  | .abstraction τ e => do
      let ⟨τ', e'⟩ ← infer (τ :: Γ) e
      some ⟨_, Expr.abstraction e'⟩
  | .application e₁ e₂ => do
      let ⟨τ, e₁'⟩ ← infer Γ e₁

      match τ with
      | .number | .string => none
      | .arrow τ τ' =>
          let e₂' ← check Γ e₂ τ
          some ⟨_, Expr.application e₁' e₂'⟩

def check (Γ : Context) : (e : Bound.Expr Γ.length) → (τ : Ty) → Option (Γ ⊢ τ)
  | .var i, τ =>
      let { τ := τ', a } := Any.from_fin Γ i
      match decEq τ τ' with
      | isTrue eq => some (by subst_vars; exact Expr.var a)
      | isFalse _ => none
  | .number num, τ =>
      match decEq τ Ty.number with
      | isTrue eq => by subst_vars; exact some (Expr.number num)
      | isFalse _ => none
  | .string s, τ =>
      match decEq τ Ty.string with
      | isTrue eq => by subst_vars; exact some (Expr.string s)
      | isFalse _ => none
  | .abstraction τ₁ e, Ty.arrow τ₁' τ₂ =>
      match decEq τ₁ τ₁' with
      | isTrue eq => do
          let e' ← check (τ₁' :: Γ) e τ₂
          some (by subst_vars; exact Expr.abstraction e')
      | isFalse _ => none
  | .abstraction _ _, Ty.number => none
  | .abstraction _ _, Ty.string => none
  | .application e₁ e₂, τ' => do
      let ⟨τ, e₂'⟩ ← infer Γ e₂
      let e₁' ← check Γ e₁ (Ty.arrow τ τ')
      some (Expr.application e₁' e₂')

end

mutual

def infer_sound {Γ : Context} {τ : Ty} : (e : Γ ⊢ τ) → infer Γ e.erase = some ⟨τ, e⟩
  | .var a => by simp only [erase, infer]; rw [Any.to_from_fin_inverse]
  | .number _ | .string _ => by simp only [erase, infer]
  | .abstraction e => by simp only [erase, infer, infer_sound e, Bind.bind, Option.bind]
  | .application e₁ e₂ => by simp only [erase, infer, infer_sound e₁, check_sound e₂, Bind.bind, Option.bind]

def check_sound {Γ : Context} {τ : Ty} : (t : Γ ⊢ τ) → check Γ t.erase τ = some t
  | .var a => by
      simp only [erase, check]
      rw [Any.to_from_fin_inverse]
      cases decEq τ τ with
      | isTrue => rfl
      | isFalse => contradiction
  | .number _ => by
      simp only [erase, check]
      match decEq Ty.number Ty.number with
      | isTrue _ => simp only
      | isFalse _ => contradiction
  | .string _ => by
      simp only [erase, check]
      match decEq Ty.string Ty.string with
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
  | .var a | .number _ | .string _ => unfold erase infer at *; subst_vars; contradiction
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
  | .number _ | .string _ => unfold erase check at *; subst eq; contradiction
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
