import E.Dynamics.Normal
import E.Dynamics.Normalization
import E.Dynamics.Progress
import E.Statics

open Statics

namespace Dynamics

inductive Env : Context -> Type where
  | nil  : Env []
  | cons {Γ : Context} {τ : Ty} {t : Γ ⊢ τ} : (val : Value t) -> (env : Env Γ) -> Env (τ :: Γ)

infixr:67 " :: " => Env.cons

namespace Env

def get {Γ : Context} {τ : Ty} : (env : Env Γ) → (a : Γ ∋ τ) → Σ t : Γ ⊢ τ, Value t
  | @cons _ _ t val _, .here => ⟨t.shift, Value.renamed Rename.shift val⟩
  | cons _ env, .there a =>
      let ⟨t, val⟩ := env.get a
      ⟨t.shift, Value.renamed Rename.shift val⟩

def subst {Γ : Context} : Env Γ → ClosingSubst Γ
  | val :: _, _, .here => val.strip_context.1
  | _ :: env, _, .there a => subst env a

end Env

abbrev _root_.Statics.Typing.close {Γ : Context} {τ : Ty} (env : Env Γ) (t : Γ ⊢ τ) : ⊢ τ := Typing.subst env.subst t

def _root_.Statics.Typing.eval_closed {τ : Ty} (t : ⊢ τ) : Σ t' : ⊢ τ, Value t' :=
  match t.progress with
  | @Progress.step _ _ t' tr =>
      have := tr.step_count_decreases
      t'.eval_closed
  | .done val => ⟨_, val⟩

termination_by eval_closed => t.step_count

def _root_.Statics.Typing.eval {Γ : Context} {τ : Ty} (env : Env Γ) (t : Γ ⊢ τ) : Σ t' : ⊢ τ, Value t' := Typing.eval_closed (Typing.close env t)
