import Aesop
import Vect

import Stlc.Bound
import Stlc.Statics
import Stlc.Syntax

open Bound (Expr)
open Statics (Ty TyOperator)
open Syntax (Ident)

namespace ScopeCheck

abbrev Binder : Nat → Type := Vect Ident

inductive Scoping : {n : Nat} → Binder n → Syntax.Expr → Expr n → Type where
  | var_zero
      {n : Nat} {Γ : Binder n} {x : Ident} :
      Scoping (x ::ᵥ Γ) (Syntax.Expr.var x) (Expr.var 0)

  | var_succ
      {n : Nat} {Γ : Binder n} {x y : Ident} {i : Fin n} :
      x ≠ y →
      Scoping Γ (Syntax.Expr.var x) (Expr.var i) →
      Scoping (y ::ᵥ Γ) (Syntax.Expr.var x) (Expr.var i.succ)

  | triv
      {n : Nat} {Γ : Binder n} :
      Scoping Γ Syntax.Expr.triv Expr.triv

  | pair
      {n : Nat} {Γ : Binder n} {e₁ e₂ : Syntax.Expr} {e₁' e₂' : Expr n} :
      Scoping Γ e₁ e₁' →
      Scoping Γ e₂ e₂' →
      Scoping Γ (Syntax.Expr.pair e₁ e₂) (Expr.pair e₁' e₂')

  | projₗ
      {n : Nat} {Γ : Binder n} {e : Syntax.Expr} {e' : Expr n} :
      Scoping Γ e e' →
      Scoping Γ (Syntax.Expr.projₗ e) (Expr.projₗ e')

  | projᵣ
      {n : Nat} {Γ : Binder n} {e : Syntax.Expr} {e' : Expr n} :
      Scoping Γ e e' →
      Scoping Γ (Syntax.Expr.projᵣ e) (Expr.projᵣ e')

  | nullary_case
      {n : Nat} {Γ : Binder n} {τ : Ty} {e : Syntax.Expr} {e' : Expr n} :
      Scoping Γ e e' →
      Scoping Γ (Syntax.Expr.nullary_case τ e) (Expr.nullary_case τ e')

  | inl
      {n : Nat} {Γ : Binder n} {τₗ τᵣ : Ty} {e : Syntax.Expr} {e' : Expr n} :
      Scoping Γ e e' →
      Scoping Γ (Syntax.Expr.inₗ τₗ τᵣ e) (Expr.inₗ τₗ τᵣ e')

  | inr
      {n : Nat} {Γ : Binder n} {τₗ τᵣ : Ty} {e : Syntax.Expr} {e' : Expr n} :
      Scoping Γ e e' →
      Scoping Γ (Syntax.Expr.inᵣ τₗ τᵣ e) (Expr.inᵣ τₗ τᵣ e')

  | binary_case
      {n : Nat} {Γ : Binder n} {x₁ x₂ : Ident} {e eₗ eᵣ : Syntax.Expr} {e' : Expr n} {eₗ' eᵣ' : Expr n.succ} :
      Scoping Γ e e' →
      Scoping (x₁ ::ᵥ Γ) eₗ eₗ' →
      Scoping (x₂ ::ᵥ Γ) eᵣ eᵣ' →
      Scoping Γ (Syntax.Expr.binary_case e x₁ eₗ x₂ eᵣ) (Expr.binary_case e' eₗ' eᵣ')

  | generic_ext
      {n : Nat} {Γ : Binder n} {x : Ident} {τ: Ty} {e₁ e₂ : Syntax.Expr} {e₁' : Expr n.succ} {e₂' : Expr n}
      (τ_op : TyOperator) :
      Scoping (x ::ᵥ Γ) e₁ e₁' →
      Scoping Γ e₂ e₂' →
      Scoping Γ (Syntax.Expr.generic_ext τ_op x τ e₁ e₂) (Expr.generic_ext τ_op τ e₁' e₂')

  | abstraction
      {n : Nat} {Γ : Binder n} {x : Ident} {τ : Ty} {e : Syntax.Expr} {e' : Expr n.succ} :
      Scoping (x ::ᵥ Γ) e e' →
      Scoping Γ (Syntax.Expr.abstraction x τ e) (Expr.abstraction τ e')

  | application
      {n : Nat} {Γ : Binder n} {e₁ e₂ : Syntax.Expr} {e₁' e₂' : Expr n} :
      Scoping Γ e₁ e₁' →
      Scoping Γ e₂ e₂' →
      Scoping Γ (Syntax.Expr.application e₁ e₂) (Expr.application e₁' e₂')

notation:40 Γ " ⊢ " e₁ " ↝ " e₂ => Scoping Γ e₁ e₂

namespace Scoping

@[aesop [safe forward, unsafe apply]]
theorem deterministic
  {n : Nat} {Γ : Binder n} {e : Syntax.Expr} {e₁' e₂' : Expr n} :
  (s₁ : Γ ⊢ e ↝ e₁') → (s₂ : Γ ⊢ e ↝ e₂') →
  e₁' = e₂'
  | .var_zero, .var_zero => rfl
  | .var_succ _ s, .var_succ _ s' => by
      have := deterministic s s'
      simp_all only [Expr.var.injEq]
  | .triv, .triv => rfl
  | .pair sₗ sᵣ, .pair sₗ' sᵣ' => by rw [deterministic sₗ sₗ', deterministic sᵣ sᵣ']
  | .projₗ s, .projₗ s' => by rw [deterministic s s']
  | .projᵣ s, .projᵣ s' => by rw [deterministic s s']
  | .nullary_case s, .nullary_case s' => by rw [deterministic s s']
  | .inl s, .inl s' => by rw [deterministic s s']
  | .inr s, .inr s' => by rw [deterministic s s']
  | .binary_case s s₁ s₂, .binary_case s' s₁' s₂' => by rw [deterministic s s', deterministic s₁ s₁', deterministic s₂ s₂']
  | .generic_ext τ_op s₁ s₂, .generic_ext _ s₁' s₂' => by rw [deterministic s₁ s₁', deterministic s₂ s₂']
  | .abstraction s, .abstraction s' => by rw [deterministic s s']
  | .application s₁ s₂, .application s₁' s₂' => by rw [deterministic s₁ s₁', deterministic s₂ s₂']

@[aesop safe [apply, forward]]
theorem irrelevant
  {n : Nat} {Γ : Binder n} {e : Syntax.Expr} {e' : Expr n}
  (s s' : Γ ⊢ e ↝ e') :
  s = s'
:= by
  induction s with
  | var_zero =>
      cases s'
      rfl
  | @var_succ _ _ _ _ i _ s ih =>
      cases i
      cases s' with
      | var_succ _ s' => rw [ih s']
  | triv =>
      cases s'
      aesop
  | pair =>
      cases s'
      aesop
  | projₗ =>
      cases s'
      aesop
  | projᵣ =>
      cases s'
      aesop
  | nullary_case =>
      cases s'
      aesop
  | inl =>
      cases s'
      aesop
  | inr =>
      cases s'
      aesop
  | binary_case =>
      cases s'
      aesop
  | generic_ext =>
      cases s'
      aesop
  | abstraction =>
      cases s'
      aesop
  | application =>
      cases s'
      aesop

@[local aesop norm simp]
private def find_name {n : Nat} : (Γ : Binder n) → (x : Ident) → Option (Σ' e' : Expr n, Γ ⊢ Syntax.Expr.var x ↝ e')
  | []ᵥ, x => none
  | (y ::ᵥ Γ), x => match String.decEq x y with
      | isFalse ne => do
          let ⟨Expr.var i, s⟩ ← find_name Γ x
          some ⟨Expr.var i.succ, .var_succ ne s⟩
      | isTrue eq => some ⟨Expr.var 0, by subst_vars; exact .var_zero⟩

@[local aesop [safe destruct, unsafe apply]]
private def find_name_complete
  {n : Nat} {Γ : Binder n} {x : Ident} {e' : Expr n}
  (h : find_name Γ x = none) (s : Γ ⊢ Syntax.Expr.var x ↝ e') :
  Empty
:= by
  cases Γ with
  | nil => cases s
  | cons y Γ =>
      unfold find_name at h
      split at h
      . cases s with
        | var_zero => contradiction
        | var_succ _ s =>
            simp only [Bind.bind, Option.bind] at h
            split at h
            . rename_i g
              exact find_name_complete g s
            . aesop
      . simp_all only

@[local aesop norm simp]
def infer {n : Nat} (Γ : Binder n) : (e : Syntax.Expr) → Option (Σ' e' : Expr n, Γ ⊢ e ↝ e')
  | .var x => find_name Γ x
  | .triv => some ⟨Expr.triv, Scoping.triv⟩
  | .pair e₁ e₂ => do
      let ⟨e₁', p₁⟩ ← infer Γ e₁
      let ⟨e₂', p₂⟩ ← infer Γ e₂
      some ⟨Expr.pair e₁' e₂', Scoping.pair p₁ p₂⟩
  | .projₗ e => do
      let ⟨e', p⟩ ← infer Γ e
      some ⟨Expr.projₗ e', Scoping.projₗ p⟩
  | .projᵣ e => do
      let ⟨e', p⟩ ← infer Γ e
      some ⟨Expr.projᵣ e', Scoping.projᵣ p⟩
  | .nullary_case τ e => do
      let ⟨e', p⟩ ← infer Γ e
      some ⟨Expr.nullary_case τ e', .nullary_case p⟩
  | .inₗ τₗ τᵣ e => do
      let ⟨e', p⟩ ← infer Γ e
      some ⟨Expr.inₗ τₗ τᵣ e', .inl p⟩
  | .inᵣ τₗ τᵣ e => do
      let ⟨e', p⟩ ← infer Γ e
      some ⟨Expr.inᵣ τₗ τᵣ e', .inr p⟩
  | .binary_case e xₗ eₗ xᵣ eᵣ => do
      let ⟨e', s⟩ ← infer Γ e
      let ⟨eₗ', sₗ⟩ ← infer (xₗ ::ᵥ Γ) eₗ
      let ⟨eᵣ', sᵣ⟩ ← infer (xᵣ ::ᵥ Γ) eᵣ
      some ⟨Expr.binary_case e' eₗ' eᵣ', .binary_case s sₗ sᵣ⟩
  | .generic_ext τ_op x τ e₁ e₂ => do
      let ⟨e₁', s₁⟩ ← infer (x ::ᵥ Γ) e₁
      let ⟨e₂', s₂⟩ ← infer Γ e₂
      some ⟨Expr.generic_ext τ_op τ e₁' e₂', .generic_ext τ_op s₁ s₂⟩
  | .abstraction x τ e => do
      let ⟨e', p⟩ ← infer (x ::ᵥ Γ) e
      some ⟨Expr.abstraction τ e', .abstraction p⟩
  | .application e₁ e₂ => do
      let ⟨e₁', s₁⟩ ← infer Γ e₁
      let ⟨e₂', s₂⟩ ← infer Γ e₂
      some ⟨Expr.application e₁' e₂', .application s₁ s₂⟩

@[aesop [safe destruct, unsafe apply]]
def infer_complete
  {n : Nat} {Γ : Binder n} {e : Syntax.Expr} {e' : Expr n}
  (h : infer Γ e = none) (s : Γ ⊢ e ↝ e') :
  Empty
:= by
  cases s with
  | var_zero => simp [infer, find_name, String.decEq] at h
  | var_succ => aesop (add norm simp [Bind.bind, Option.bind])
  | triv => contradiction
  | @pair _ Γ e₁ e₂ _ _ s₁ s₂ =>
      match g₁ : infer Γ e₁, g₂ : infer Γ e₂ with
      | some _, some _ => simp only [g₁, g₂, infer, Bind.bind, Option.bind] at h
      | none, _ => exact infer_complete g₁ s₁
      | _, none => exact infer_complete g₂ s₂
  | @projₗ _ Γ e _ s =>
      match g : infer Γ e with
      | some _ => simp only [g, infer, Bind.bind, Option.bind] at h
      | none => exact infer_complete g s
  | @projᵣ _ Γ e _ s =>
      match g : infer Γ e with
      | some _ => simp only [g, infer, Bind.bind, Option.bind] at h
      | none => exact infer_complete g s
  | @nullary_case _ Γ _ e _ s =>
      match g : infer Γ e with
      | some _ => simp only [g, infer, Bind.bind, Option.bind] at h
      | none => exact infer_complete g s
  | @inl _ Γ _ _ e _ s =>
      match g : infer Γ e with
      | some _ => simp only [g, infer, Bind.bind, Option.bind] at h
      | none => exact infer_complete g s
  | @inr _ Γ _ _ e _ s =>
      match g : infer Γ e with
      | some _ => simp only [g, infer, Bind.bind, Option.bind] at h
      | none => exact infer_complete g s
  | @binary_case _ Γ xₗ xᵣ e eₗ eᵣ _ _ _ s sₗ sᵣ =>
      match g : infer Γ e, gₗ : infer (xₗ ::ᵥ Γ) eₗ, gᵣ : infer (xᵣ ::ᵥ Γ) eᵣ with
      | some _, some _, some _ => simp only [g, gₗ, gᵣ, infer, Bind.bind, Option.bind] at h
      | none, _, _ => exact infer_complete g s
      | _, none, _ => exact infer_complete gₗ sₗ
      | _, _, none => exact infer_complete gᵣ sᵣ
  | @generic_ext _ Γ x _ e₁ e₂ _ _ _ s₁ s₂ =>
      match g₁ : infer (x ::ᵥ Γ) e₁, g₂ : infer Γ e₂ with
      | some _, some _ => simp only [g₁, g₂, infer, Bind.bind, Option.bind] at h
      | none, _ => exact infer_complete g₁ s₁
      | _, none => exact infer_complete g₂ s₂
  | @abstraction _ Γ x _ e _ s =>
      match g : infer (x ::ᵥ Γ) e with
      | some _ => simp only [g, infer, Bind.bind, Option.bind] at h
      | none => exact infer_complete g s
  | @application _ Γ e₁ e₂ _ _ s₁ s₂ =>
      match g₁ : infer Γ e₁, g₂ : infer Γ e₂ with
      | some _, some _ => simp only [g₁, g₂, infer, Bind.bind, Option.bind] at h
      | none, _ => exact infer_complete g₁ s₁
      | _, none => exact infer_complete g₂ s₂

@[simp]
theorem infer_sound
  {n : Nat} {Γ : Binder n} {e : Syntax.Expr} {e' : Expr n}
  (h : Γ ⊢ e ↝ e') :
  infer Γ e = .some ⟨e', h⟩
:= by
  induction h with unfold infer
  | var_zero => simp [find_name, String.decEq]
  | @var_succ _ _ x y _ _ _ h =>
      unfold find_name
      split
      . aesop
      . contradiction
  | triv => rfl
  | pair p₁ p₂ ih₁ ih₂ => rw [ih₁, ih₂]; rfl
  | projₗ p ih => rw [ih]; rfl
  | projᵣ p ih => rw [ih]; rfl
  | nullary_case _ ih => rw [ih]; rfl
  | inl _ ih => rw [ih]; rfl
  | inr _ ih => rw [ih]; rfl
  | binary_case _ _ _ ih ih₁ ih₂ => rw [ih, ih₁, ih₂]; rfl
  | generic_ext _ _ _ ih₁ ih₂ => rw [ih₁, ih₂]; rfl
  | abstraction _ ih => rw [ih]; rfl
  | application _ _ ih₁ ih₂ => rw [ih₁, ih₂]; rfl

@[local aesop norm simp]
def check {n : Nat} (Γ : Binder n) (e : Syntax.Expr) (e' : Expr n) : Option (Γ ⊢ e ↝ e') :=
  match infer Γ e with
  | some ⟨e'', p⟩ =>
      match decEq e' e'' with
      | isTrue eq => some (by subst_vars; exact p)
      | isFalse _ => none
  | none => none

@[aesop [safe destruct, unsafe apply]]
def check_complete
  {n : Nat} {Γ : Binder n} {e : Syntax.Expr} {e' : Expr n}
  (h : check Γ e e' = none) (s : Γ ⊢ e ↝ e') :
  Empty
:= by
  simp_all only [check]
  aesop

@[simp]
theorem check_sound
  {n : Nat} {Γ : Binder n} {e : Syntax.Expr} {e' : Expr n}
  (h : Γ ⊢ e ↝ e') :
  check Γ e e' = .some h
:= by
  aesop

end Scoping
