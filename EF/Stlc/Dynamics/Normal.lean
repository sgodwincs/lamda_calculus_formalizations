import Aesop

import Stlc.Statics

open Statics

namespace Dynamics

inductive Value {Γ : Context} : {τ : Ty} → (Γ ⊢ τ) → Type where
  | number
      {num : Nat} :
      Value (@Expr.number Γ num)
  
  | string
      {s : String} :
      Value (@Expr.string Γ s)
  
  | abstraction
      {τ τ' : Ty} {e : τ :: Γ ⊢ τ'} :
      Value (Expr.abstraction e)
  deriving DecidableEq, Repr

namespace Value

def rename
  {Γ Δ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (ρ : Rename Γ Δ) :
  (val : Value e) →
  Value (Expr.rename ρ e)
  | .number => by dsimp only [Expr.rename]; exact Value.number
  | .string => by dsimp only [Expr.rename]; exact Value.string
  | .abstraction => by dsimp only [Expr.rename]; exact Value.abstraction

end Value

mutual

  inductive Normal : {Γ : Context} → {τ : Ty} → (Γ ⊢ τ) → Type where
  | neutral
      {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
      Neutral e →
      Normal e
  
  | value
      {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
      Value e →
      Normal e
  deriving Repr

  inductive Neutral : {Γ : Context} → {τ : Ty} → (Γ ⊢ τ) → Type where
  | var
      {Γ : Context} {τ : Ty} (a : Γ ∋ τ) :
      Neutral (Expr.var a)
  
  | application
      {Γ : Context} {τ τ' : Ty} {e₁ : Γ ⊢ Ty.arrow τ τ'} {e₂ : Γ ⊢ τ} :
      Neutral e₁ →
      Normal e₂ →
      Neutral (Expr.application e₁ e₂)
  deriving Repr
  
end

mutual

def Normal.decEq {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} (norm norm' : Normal e) : Decidable (norm = norm') :=
  match norm with
  | .value val => by
      cases norm' with
      | value val' =>
          match decEq val val' with
          | isTrue eq => rw [eq]; exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Normal.value.injEq])
      | _ => exact isFalse (by simp only)
  | .neutral neut => by
      cases norm' with
      | neutral neut' =>
          match Neutral.decEq neut neut' with
          | isTrue eq => rw [eq]; exact isTrue rfl
          | isFalse ne => exact isFalse (by simp_all only [Normal.neutral.injEq])
      | _ => exact isFalse (by simp only)

def Neutral.decEq {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} (neut neut' : Neutral e) : Decidable (neut = neut') :=
  match τ, e, neut with
  | _, _, .var _ => by cases neut'; exact isTrue rfl
  | _, _, .application neut₁ norm₂ => by
      cases neut' with
      | application neut₁' norm₂' =>
          match Neutral.decEq neut₁ neut₁', Normal.decEq norm₂ norm₂' with
          | isTrue eq, isTrue eq' => rw [eq, eq']; exact isTrue rfl
          | isFalse ne, _ => exact isFalse (by simp_all only [Neutral.application.injEq, false_and])
          | _, isFalse ne => exact isFalse (by simp_all only [Neutral.application.injEq, and_false])

end

instance {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) : DecidableEq (Normal e) := Normal.decEq

instance {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) : DecidableEq (Neutral e) := Neutral.decEq

mutual

def Normal.rename
  {Γ Δ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (ρ : Rename Γ Δ) :
  (norm : Normal e) →
  Normal (Expr.rename ρ e)
  | .neutral neut => by exact Normal.neutral (Neutral.rename ρ neut)
  | .value val => by exact Normal.value (Value.rename ρ val)

def Neutral.rename
  {Γ Δ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (ρ : Rename Γ Δ) :
  (neut : Neutral e) →
  Neutral (Expr.rename ρ e)
  | .var a => by dsimp only [Expr.rename]; exact Neutral.var (ρ a)
  | .application neut₁ norm₂ => by
      dsimp only [Expr.rename]
      exact Neutral.application (Neutral.rename ρ neut₁) (Normal.rename ρ norm₂)

end

def Value.normal
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (val : Value e) :
  Normal e := Normal.value val

def Value.not_neutral
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
  Value e →
  Neutral e →
  Empty
  | .number, neut => nomatch neut
  | .string, neut => nomatch neut
  | .abstraction, neut => nomatch neut

def Neutral.normal
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (neut : Neutral e) :
  Normal e := Normal.neutral neut

def Neutral.not_a_value
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (neut : Neutral e)
  (val : Value e) :
  Empty := val.not_neutral neut

theorem Value.irrelevant
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
  (val val' : Value e) →
  val = val'
  | .number, .number => rfl
  | .string, .string => rfl
  | .abstraction, .abstraction => rfl

mutual

  theorem Normal.irrelevant
    {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
    (norm norm' : Normal e) →
    norm = norm'
    | .neutral neut, .neutral neut' => by rw [Neutral.irrelevant neut neut']
    | .neutral neut, .value val' => Empty.elim (Value.not_neutral val' neut)
    | .value val, .value val' => by rw [Value.irrelevant val val']
    | .value val, .neutral neut' => Empty.elim (Value.not_neutral val neut')

  theorem Neutral.irrelevant
    {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} :
    (neut neut' : Neutral e) →
    neut = neut'
    | .var _, .var _ => rfl
    | .application neut₁ norm₂, .application neut₁' norm₂' => by rw [Neutral.irrelevant neut₁ neut₁', Normal.irrelevant norm₂ norm₂']

end
