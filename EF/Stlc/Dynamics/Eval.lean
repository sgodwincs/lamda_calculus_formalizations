import Stlc.Dynamics.Normal
import Stlc.Dynamics.Normalization
import Stlc.Dynamics.Progress
import Stlc.Statics

open Statics

namespace Dynamics

inductive Env : Context -> Type where
  | nil  : Env []
  | cons {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} : (val : Value e) -> (env : Env Γ) -> Env (τ :: Γ)

infixr:67 " :: " => Env.cons

namespace Env

def get {Γ : Context} {τ : Ty} : (env : Env Γ) → (a : Γ ∋ τ) → Σ t : Γ ⊢ τ, Value t
  | @cons _ _ e val _, .here => ⟨e.shift, Value.rename Rename.shift val⟩
  | cons _ env, .there a =>
      let ⟨e, val⟩ := env.get a
      ⟨e.shift, Value.rename Rename.shift val⟩

end Env

mutual

def Env.subst {Γ : Context} : Env Γ → ClosingSubst Γ
  | val :: env, _, .here => (Value.close env val).1
  | _ :: env, _, .there a => Env.subst env a

def Value.close {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} (env : Env Γ) : Value e → Σ e' : ⊢ τ, Value e'
  | @Value.number _ num => ⟨_, @Value.number _ num⟩
  | @Value.string _ s => ⟨_, @Value.string _ s⟩
  | @Value.abstraction _ τ _ e => ⟨_, @Value.abstraction _ _ _ (Expr.subst (Subst.exts env.subst) e)⟩

end

abbrev _root_.Statics.Expr.close {Γ : Context} {τ : Ty} (env : Env Γ) (t : Γ ⊢ τ) : ⊢ τ := Expr.subst env.subst t

structure EvalResult {Γ : Context} (τ : Ty) (env : Env Γ) where
  {e : Γ ⊢ τ}
  val : Value e

abbrev ClosedEvalResult (τ : Ty) := EvalResult τ Env.nil

def _root_.Statics.Expr.eval_closed {τ : Ty} (e : ⊢ τ) : Σ e' : ⊢ τ, Value e' :=
  match e.progress with
  | @Progress.step _ _ e' tr =>
      have := tr.step_count_decreases
      e'.eval_closed
  | .done val => ⟨_, val⟩

termination_by eval_closed => e.step_count

def _root_.Statics.Expr.eval {Γ : Context} {τ : Ty} (env : Env Γ) (e : Γ ⊢ τ) : Σ e' : ⊢ τ, Value e' :=
  Expr.eval_closed (Expr.close env e)
