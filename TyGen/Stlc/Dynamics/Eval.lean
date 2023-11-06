import Mathlib.Tactic
import Stlc.Dynamics.Normal
import Stlc.Dynamics.Normalization
import Stlc.Dynamics.Progress
import Stlc.Statics

open Statics

namespace Dynamics

inductive Env : Context -> Type where
  | nil  : Env []
  | cons {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} : (val : Value e) -> (env : Env Γ) -> Env (τ :: Γ)

notation "[]ₑ" => Env.nil
infixr:67 " ::ₑ " => Env.cons

namespace Env

def get {Γ : Context} {τ : Ty} : (env : Env Γ) → (a : Γ ∋ τ) → Σ t : Γ ⊢ τ, Value t
  | @cons _ _ e val _, .here => ⟨e.shift, Value.rename Rename.shift val⟩
  | cons _ env, .there a =>
      let ⟨e, val⟩ := env.get a
      ⟨e.shift, Value.rename Rename.shift val⟩

end Env

mutual

def Env.subst {Γ : Context} : Env Γ → ClosingSubst Γ
  | val ::ₑ env, _, .here => (Value.close env val).1
  | _ ::ₑ env, _, .there a => Env.subst env a

def Value.close {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} (env : Env Γ) : Value e → Σ e' : ⊢ τ, Value e'
  | .triv => ⟨_, .triv⟩
  | .pair val₁ val₂ => ⟨_, .pair (val₁.close env).2 (val₂.close env).2⟩
  | .inₗ val => ⟨_, Value.inₗ (val.close env).2⟩
  | .inᵣ val => ⟨_, Value.inᵣ (val.close env).2⟩
  | @Value.abstraction _ τ τ' e => by
      have : 1 < 1 + sizeOf τ + sizeOf τ' + sizeOf e := by linarith [Expr.sizeOf_ge_1 e]
      exact ⟨_, @Value.abstraction _ _ _ (Expr.subst (Subst.exts env.subst) e)⟩

end

termination_by Env.subst _ env _ _ => sizeOf (env, 1)
               Value.close val => sizeOf (env, val)

abbrev _root_.Statics.Expr.close {Γ : Context} {τ : Ty} (env : Env Γ) (t : Γ ⊢ τ) : ⊢ τ := Expr.subst env.subst t

structure EvalResult {Γ : Context} (τ : Ty) (env : Env Γ) where
  {e : Γ ⊢ τ}
  val : Value e

abbrev ClosedEvalResult (τ : Ty) := EvalResult τ []ₑ

def _root_.Statics.Expr.eval_closed {τ : Ty} (e : ⊢ τ) : Σ e' : ⊢ τ, Value e' :=
  match e.progress with
  | @Progress.step _ _ e' tr =>
      have := tr.step_count_decreases
      e'.eval_closed
  | .done val => ⟨_, val⟩

termination_by eval_closed => e.step_count

def _root_.Statics.Expr.eval {Γ : Context} {τ : Ty} (env : Env Γ) (e : Γ ⊢ τ) : Σ e' : ⊢ τ, Value e' :=
  Expr.eval_closed (Expr.close env e)
