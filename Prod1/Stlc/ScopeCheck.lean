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

  | triv
      {n : Nat} {Γ : Binder n} :
      Scoping Γ Syntax.Expr.triv Expr.triv

  | pair
      {n : Nat} {Γ : Binder n} {e₁ e₂ : Syntax.Expr} {e₁' e₂' : Expr n} :
      Scoping Γ e₁ e₁' →
      Scoping Γ e₂ e₂' →
      Scoping Γ (Syntax.Expr.pair e₁ e₂) (Expr.pair e₁' e₂')

  | proj₁
      {n : Nat} {Γ : Binder n} {e : Syntax.Expr} {e' : Expr n} :
      Scoping Γ e e' →
      Scoping Γ (Syntax.Expr.proj₁ e) (Expr.proj₁ e')

  | proj₂
      {n : Nat} {Γ : Binder n} {e : Syntax.Expr} {e' : Expr n} :
      Scoping Γ e e' →
      Scoping Γ (Syntax.Expr.proj₂ e) (Expr.proj₂ e')

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
  | triv => cases h₂; rfl
  | pair p₁ p₂ ih₁ ih₂ => cases h₂ with
    | pair p₁' p₂' => rw [ih₁ p₁', ih₂ p₂']
  | proj₁ p ih => cases h₂ with
    | proj₁ p' => rw [ih p']
  | proj₂ p ih => cases h₂ with
    | proj₂ p' => rw [ih p']
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
  | .triv => some ⟨Expr.triv, Scoping.triv⟩
  | .pair e₁ e₂ => do
      let ⟨e₁', p₁⟩ ← infer Γ e₁
      let ⟨e₂', p₂⟩ ← infer Γ e₂
      some ⟨Expr.pair e₁' e₂', Scoping.pair p₁ p₂⟩
  | .proj₁ e => do
      let ⟨e', p⟩ ← infer Γ e
      some ⟨Expr.proj₁ e', Scoping.proj₁ p⟩
  | .proj₂ e => do
      let ⟨e', p⟩ ← infer Γ e
      some ⟨Expr.proj₂ e', Scoping.proj₂ p⟩
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
  | triv => contradiction
  | @pair _ Γ e₁ e₂ =>
      match g₁ : infer Γ e₁, g₂ : infer Γ e₂ with
      | some _, some _ => rw [g₁, g₂] at h₁; injection h₁
      | none, _ => contradiction
      | _, none => contradiction
  | @proj₁ _ Γ e =>
      match g : infer Γ e with
      | some _ => rw [g] at h₁; injection h₁
      | none => contradiction
  | @proj₂ _ Γ e =>
      match g : infer Γ e with
      | some _ => rw [g] at h₁; injection h₁
      | none => contradiction
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
  | triv => rfl
  | pair p₁ p₂ ih₁ ih₂ => rw [ih₁, ih₂]; rfl
  | proj₁ p ih => rw [ih]; rfl
  | proj₂ p ih => rw [ih]; rfl
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
