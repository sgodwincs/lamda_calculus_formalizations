import E.Bound
import E.Statics

namespace Statics.Typing

def erase {Γ : Context} {τ : Ty} : (Γ ⊢ τ) → Bound.Expr Γ.length
  | .var a => Bound.Expr.var a.to_fin
  | .number num => Bound.Expr.number num
  | .string s => Bound.Expr.string s
  | .plus t₁ t₂ => Bound.Expr.plus (erase t₁) (erase t₂)
  | .times t₁ t₂ => Bound.Expr.times (erase t₁) (erase t₂)
  | .concatenate t₁ t₂ => Bound.Expr.concatenate (erase t₁) (erase t₂)
  | .length t => Bound.Expr.length (erase t)
  | .let t₁ t₂ => Bound.Expr.let (erase t₁) (erase t₂)

mutual

def infer (Γ : Context) : (e : Bound.Expr Γ.length) → Option (Σ τ : Ty, Γ ⊢ τ)
  | .var i =>
      let ⟨τ, a⟩ := Any.from_fin Γ i
      some ⟨τ, Typing.var a⟩
  | .number num => some ⟨Ty.number, Typing.number num⟩
  | .string s => some ⟨Ty.string, Typing.string s⟩
  | .plus e₁ e₂ => do
      let t₁ ← check Γ e₁ Ty.number
      let t₂ ← check Γ e₂ Ty.number
      some ⟨Ty.number, Typing.plus t₁ t₂⟩
  | .times e₁ e₂ => do
      let t₁ ← check Γ e₁ Ty.number
      let t₂ ← check Γ e₂ Ty.number
      some ⟨Ty.number, Typing.times t₁ t₂⟩
  | .concatenate e₁ e₂ => do
      let t₁ ← check Γ e₁ Ty.string
      let t₂ ← check Γ e₂ Ty.string
      some ⟨Ty.string, Typing.concatenate t₁ t₂⟩
  | .length e => do
      let t ← check Γ e Ty.string
      some ⟨Ty.number, Typing.length t⟩
  | .let e₁ e₂ => do
      let ⟨τ₁, t₁⟩ ← infer Γ e₁
      let ⟨τ₂, t₂⟩ ← infer (τ₁ :: Γ) e₂
      some ⟨τ₂, Typing.let t₁ t₂⟩

def check (Γ : Context) : (e : Bound.Expr Γ.length) → (τ : Ty) → Option (Γ ⊢ τ)
  | .var i, τ =>
      let ⟨τ', a⟩ := Any.from_fin Γ i
      match decEq τ τ' with
      | isTrue eq => some (by rw [eq]; exact Typing.var a)
      | isFalse _ => none
  | .number num, Ty.number => some (Typing.number num)
  | .number _, Ty.string => none
  | .string s, Ty.string => some (Typing.string s)
  | .string _, Ty.number => none
  | .plus e₁ e₂, Ty.number => do
      let t₁ ← check Γ e₁ Ty.number
      let t₂ ← check Γ e₂ Ty.number
      some (Typing.plus t₁ t₂)
  | .plus _ _, Ty.string => none
  | .times e₁ e₂, Ty.number => do
      let t₁ ← check Γ e₁ Ty.number
      let t₂ ← check Γ e₂ Ty.number
      some (Typing.times t₁ t₂)
  | .times _ _, Ty.string => none
  | .concatenate e₁ e₂, Ty.string => do
      let t₁ ← check Γ e₁ Ty.string
      let t₂ ← check Γ e₂ Ty.string
      some (Typing.concatenate t₁ t₂)
  | .concatenate _ _, Ty.number => none
  | .length e, Ty.number => do
      let t ← check Γ e Ty.string
      some (Typing.length t)
  | .length _, Ty.string => none
  | .let e₁ e₂, τ₂ => do
      let ⟨τ₁, t₁⟩ ← infer Γ e₁
      let t₂ ← check (τ₁ :: Γ) e₂ τ₂
      some (Typing.let t₁ t₂)

end

mutual

def infer_sound {Γ : Context} {τ : Ty} : (t : Γ ⊢ τ) → infer Γ t.erase = some ⟨τ, t⟩
  | .var a => by simp only [erase, infer]; rw [Any.to_from_fin_inverse]
  | .number _ | .string _ => by simp only [erase, infer]
  | .plus t₁ t₂ => by simp only [erase, infer, check_sound t₁, check_sound t₂]; rfl
  | .times t₁ t₂ => by simp only [erase, infer, check_sound t₁, check_sound t₂]; rfl
  | .concatenate t₁ t₂ => by simp only [erase, infer, check_sound t₁, check_sound t₂]; rfl
  | .length t => by simp only [erase, infer, check_sound t]; rfl
  | .let t₁ t₂ => by simp only [erase, infer, infer_sound t₁, infer_sound t₂, Bind.bind, Option.bind]

def check_sound {Γ : Context} {τ : Ty} : (t : Γ ⊢ τ) → check Γ t.erase τ = some t
  | .var a => by
      simp only [erase, check]
      rw [Any.to_from_fin_inverse]
      cases decEq τ τ with
      | isTrue => rfl
      | isFalse => contradiction
  | .number _ | .string _ => by simp only [erase, check]
  | .plus t₁ t₂ => by simp only [erase, check, check_sound t₁, check_sound t₂]; rfl
  | .times t₁ t₂ => by simp only [erase, check, check_sound t₁, check_sound t₂]; rfl
  | .concatenate t₁ t₂ => by simp only [erase, check, check_sound t₁, check_sound t₂]; rfl
  | .length t => by simp only [erase, check, check_sound t]; rfl
  | .let t₁ t₂ => by simp only [erase, check, infer_sound t₁, check_sound t₂, Bind.bind, Option.bind]

end

mutual

def infer_complete
  {Γ : Context} {e : Bound.Expr Γ.length} {τ : Ty}
  (h : infer Γ e = none) :
  (Σ' t : Γ ⊢ τ, t.erase = e) → Empty :=
by
  intro ⟨t, eq⟩
  match t with
  | .var a | .number _ | .string _ => unfold erase infer at *; subst eq; contradiction
  | .plus t₁ t₂ =>
      unfold erase infer at *
      subst eq
      simp only [check_sound t₁, check_sound t₂] at h
      contradiction
  | .times t₁ t₂ =>
      unfold erase infer at *
      subst eq
      simp only [check_sound t₁, check_sound t₂] at h
      contradiction
  | .concatenate t₁ t₂ =>
      unfold erase infer at *
      subst eq
      simp only [check_sound t₁, check_sound t₂] at h
      contradiction
  | .length t =>
      unfold erase infer at *
      subst eq
      simp only [check_sound t] at h
      contradiction
  | .let t₁ t₂ =>
      unfold erase infer at *
      subst eq
      simp only [infer_sound t₁, infer_sound t₂, Bind.bind, Option.bind] at h

def check_complete
  {Γ : Context} {e : Bound.Expr Γ.length} {τ : Ty}
  (h : check Γ e τ = none) :
  (Σ' t : Γ ⊢ τ, t.erase = e) → Empty :=
by
  intro ⟨t, eq⟩
  match t with
  | .var a =>
      unfold erase check at *
      subst eq
      simp at h
      rw [Any.to_from_fin_inverse] at h
      match h' : decEq τ τ with
      | isTrue eq => subst_vars; simp_all only
      | isFalse ne => contradiction
  | .number _ | .string _ => unfold erase check at *; subst eq; contradiction
  | .plus t₁ t₂ =>
      unfold erase check at *
      subst eq
      simp only [check_sound t₁, check_sound t₂] at h
      contradiction
  | .times t₁ t₂ =>
      unfold erase check at *
      subst eq
      simp only [check_sound t₁, check_sound t₂] at h
      contradiction
  | .concatenate t₁ t₂ =>
      unfold erase check at *
      subst eq
      simp only [check_sound t₁, check_sound t₂] at h
      contradiction
  | .length t =>
      unfold erase check at *
      subst eq
      simp only [check_sound t] at h
      contradiction
  | .let t₁ t₂ =>
      unfold erase check at *
      subst eq
      simp only [infer_sound t₁, check_sound t₂, Bind.bind, Option.bind] at h

end
