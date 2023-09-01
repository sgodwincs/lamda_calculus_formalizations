import Vector

import Stlc.Bound
import Stlc.Statics
import Stlc.Syntax

open Bound (Expr)
open Statics (Ty)
open Syntax (Ident)

namespace ScopeCheck

abbrev Binder : Nat → Type := Vector Ident

inductive Scoping : {n : Nat} → Binder n → Syntax.Expr → Expr n → Prop where
  | var_zero
      {n : Nat} {Γ : Binder n} {x : Ident} :
      Scoping (x :: Γ) (Syntax.Expr.var x) (Expr.var 0)

  | var_succ
      {n : Nat} {Γ : Binder n} {x y : Ident} {i : Fin n} :
      x ≠ y →
      Scoping Γ (Syntax.Expr.var x) (Expr.var i) →
      Scoping (y :: Γ) (Syntax.Expr.var x) (Expr.var i.succ)

  | zero
      {n : Nat} {Γ : Binder n} :
      Scoping Γ Syntax.Expr.zero Expr.zero

  | succ
      {n : Nat} {Γ : Binder n} {e : Syntax.Expr} {e' : Expr n} :
      Scoping Γ e e' →
      Scoping Γ (Syntax.Expr.succ e) (Expr.succ e')

  | recursor
      {n : Nat} {Γ : Binder n} {x y : Ident} {e₁ e₂ e₃ : Syntax.Expr} {e₁' e₂' : Expr n} {e₃' : Expr n.succ.succ} :
      Scoping Γ e₁ e₁' →
      Scoping Γ e₂ e₂' →
      Scoping (y :: x :: Γ) e₃ e₃' →
      Scoping Γ (Syntax.Expr.recursor e₁ e₂ x y e₃) (Expr.recursor e₁' e₂' e₃')

  | abstraction
      {n : Nat} {Γ : Binder n} {x : Ident} {τ : Ty} {e : Syntax.Expr} {e' : Expr n.succ} :
      Scoping (x :: Γ) e e' →
      Scoping Γ (Syntax.Expr.abstraction x τ e) (Expr.abstraction τ e')

  | application
      {n : Nat} {Γ : Binder n} {e₁ e₂ : Syntax.Expr} {e₁' e₂' : Expr n} :
      Scoping Γ e₁ e₁' →
      Scoping Γ e₂ e₂' →
      Scoping Γ (Syntax.Expr.application e₁ e₂) (Expr.application e₁' e₂')

notation:40 Γ " ⊢ " e₁ " ↝ " e₂ => Scoping Γ e₁ e₂

namespace Scoping

theorem injective
  {n : Nat} {Γ : Binder n} {e : Syntax.Expr} {e₁' e₂' : Expr n}
  (h₁ : Γ ⊢ e ↝ e₁')
  (h₂ : Γ ⊢ e ↝ e₂') :
  e₁' = e₂' :=
by
  induction h₁ with
  | var_zero => cases h₂ with
    | var_zero => rfl
    | var_succ _ _ => contradiction
  | var_succ ne _ ih => cases h₂ with
    | var_zero => contradiction
    | var_succ ne' p' => congr; injection (ih p')
  | zero => cases h₂; rfl
  | succ p ih => cases h₂ with
    | succ p' => rw [ih p']
  | recursor p p₀ pₛ ih ih₀ ihₛ => cases h₂ with
    | recursor p' p₀' pₛ' => rw [ih p', ih₀ p₀', ihₛ pₛ']
  | abstraction _ ih => cases h₂ with
    | abstraction p' => rw [ih p']
  | application _ _ ih₁ ih₂ => cases h₂ with
    | application p₁' p₂' => rw [ih₁ p₁', ih₂ p₂']

private def find_name {n : Nat} : (Γ : Binder n) → (x : Ident) → Option (Σ' e' : Expr n, Γ ⊢ Syntax.Expr.var x ↝ e')
  | Vector.nil, x => none
  | (y :: Γ), x => match String.decEq x y with
      | isFalse neq => do
          let ⟨Expr.var i, p⟩ ← find_name Γ x
          some ⟨Expr.var i.succ, Scoping.var_succ neq p⟩
      | isTrue eq => some ⟨Expr.var 0, by subst eq; exact Scoping.var_zero⟩

def infer {n : Nat} (Γ : Binder n) : (e : Syntax.Expr) → Option (Σ' e' : Expr n, Γ ⊢ e ↝ e')
  | .var x => find_name Γ x
  | .zero => some ⟨Expr.zero, Scoping.zero⟩
  | .succ e => do
      let ⟨e', p⟩ ← infer Γ e
      some ⟨Expr.succ e', Scoping.succ p⟩
  | .recursor e e₀ x y eₛ => do
      let ⟨e', p⟩ ← infer Γ e
      let ⟨e₀', p₀⟩ ← infer Γ e₀
      let ⟨eₛ', pₛ⟩ ← infer (y :: x :: Γ) eₛ
      some ⟨Expr.recursor e' e₀' eₛ', Scoping.recursor p p₀ pₛ⟩
  | .abstraction x τ e => do
      let ⟨e', p⟩ ← infer (x :: Γ) e
      some ⟨Expr.abstraction τ e', Scoping.abstraction p⟩
  | .application e₁ e₂ => do
      let ⟨e₁', p₁⟩ ← infer Γ e₁
      let ⟨e₂', p₂⟩ ← infer Γ e₂
      some ⟨Expr.application e₁' e₂',Scoping.application p₁ p₂⟩

theorem infer_complete
  {n : Nat} {Γ : Binder n} {e : Syntax.Expr} {e' : Expr n}
  (h₁ : infer Γ e = none) :
  ¬ (Γ ⊢ e ↝ e') :=
by
  intro h₂
  induction h₂ with (revert h₁; unfold infer; intro h₁)
  | var_zero => revert h₁; simp [find_name, String.decEq]
  | @var_succ _ Γ x y _ _ _ ih =>
      revert h₁
      unfold infer at ih
      unfold find_name
      intro h₁
      match g₁ : String.decEq x y, g₂ : find_name Γ x with
      | isFalse h, some ⟨Expr.var i, z'⟩ => rw [g₁, g₂] at h₁; simp at h₁; injection h₁
      | isTrue _, _ => contradiction
      | _, none => contradiction
  | zero => contradiction
  | @succ _ Γ e =>
      match g : infer Γ e with
      | some _ => rw [g] at h₁; injection h₁
      | none => contradiction
  | @recursor _ Γ x y e e₀ eₛ =>
      match g₁ : infer Γ e, g₂ : infer Γ e₀, g₃ : infer (y :: x :: Γ) eₛ with
      | some _, some _, some _ => rw [g₁, g₂, g₃] at h₁; injection h₁
      | none, _, _ => contradiction
      | _, none, _ => contradiction
      | _, _, none => contradiction
  | @abstraction _ Γ x τ e =>
      match g : infer (x :: Γ) e with
      | some _ => rw [g] at h₁; injection h₁
      | none => contradiction
  | @application _ Γ e₁ e₂ =>
      match g₁ : infer Γ e₁, g₂ : infer Γ e₂ with
      | some _, some _ => rw [g₁, g₂] at h₁; injection h₁
      | none, _ => contradiction
      | _, none => contradiction

theorem infer_sound
  {n : Nat} {Γ : Binder n} {e : Syntax.Expr} {e' : Expr n}
  (h : Γ ⊢ e ↝ e') :
  infer Γ e = .some ⟨e', h⟩ :=
by
  induction h with unfold infer
  | var_zero => simp [find_name, String.decEq]
  | @var_succ _ _ x y _ _ _ ih =>
      revert ih
      unfold infer
      intro ih
      unfold find_name
      cases String.decEq x y with
      | isFalse => rw [ih]; rfl
      | isTrue => contradiction
  | zero => rfl
  | succ p ih => rw [ih]; rfl
  | recursor p p₀ pₛ ih ih₀ ihₛ => rw [ih, ih₀, ihₛ]; rfl
  | abstraction p ih => rw [ih]; rfl
  | application p₁ p₂ ih₁ ih₂ => rw [ih₁, ih₂]; rfl

instance {n : Nat} (Γ : Binder n) (e : Syntax.Expr) : Decidable (∃ e' : Expr n, Γ ⊢ e ↝ e') :=
  match h : infer Γ e with
  | some ⟨e', p⟩ => isTrue (by exact Exists.intro e' p)
  | none => isFalse (by intro ⟨e', p⟩; exact infer_complete h p)

def check {n : Nat} (Γ : Binder n) (e : Syntax.Expr) (e' : Expr n) : Option (Σ' _ : Unit, Γ ⊢ e ↝ e') :=
  match infer Γ e with
  | some ⟨e'', p⟩ =>
      match decEq e' e'' with
      | isTrue eq => some ⟨(), by rw [eq]; exact p⟩
      | isFalse _ => none
  | none => none

theorem check_complete
  {n : Nat} {Γ : Binder n} {e : Syntax.Expr} {e' : Expr n}
  (h : check Γ e e' = none) :
  ¬ (Γ ⊢ e ↝ e') :=
by
  unfold check at h
  match h' : infer Γ e with
  | some ⟨e'', p⟩ =>
      rw [h'] at h
      cases h'' : decEq e' e'' with
      | isTrue eq => simp at h; rw [h''] at h; injection h
      | isFalse ne =>
          intro p'
          have eq := Eq.symm (injective p p')
          contradiction
  | none => exact infer_complete h' 

theorem check_sound
  {n : Nat} {Γ : Binder n} {e : Syntax.Expr} {e' : Expr n}
  (h : Γ ⊢ e ↝ e') :
  check Γ e e' = .some ⟨(), h⟩ :=
by
  unfold check
  match h' : infer Γ e with
  | some ⟨e'', p⟩ =>
      simp
      cases decEq e' e'' with
      | isTrue _ => rfl
      | isFalse ne => have eq := injective h p; contradiction
  | none => simp; exact infer_complete h' h

instance {n : Nat} (Γ : Binder n) (e : Syntax.Expr) (e' : Expr n) : Decidable (Γ ⊢ e ↝ e') :=
  match h : check Γ e e' with
  | some ⟨_, p⟩ => isTrue (by exact p)
  | none => isFalse (by exact check_complete h)

end Scoping
