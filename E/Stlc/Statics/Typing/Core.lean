import Stlc.Statics.Any
import Stlc.Statics.Context
import Stlc.Statics.Ty

namespace Statics

inductive Typing : Context → Ty → Type where
  | var
      {Γ : Context} {τ : Ty} :
      (Γ ∋ τ) →
      Typing Γ τ

  | number
      {Γ : Context} :
      (num : Nat) →
      Typing Γ Ty.number
  
  | string
      {Γ : Context} :
      (s : String) →
      Typing Γ Ty.string

  | plus 
      {Γ : Context} :
      Typing Γ Ty.number →
      Typing Γ Ty.number →
      Typing Γ Ty.number

  | times 
      {Γ : Context} :
      Typing Γ Ty.number →
      Typing Γ Ty.number →
      Typing Γ Ty.number

  | concatenate
      {Γ : Context} :
      Typing Γ Ty.string →
      Typing Γ Ty.string →
      Typing Γ Ty.string

  | length
      {Γ : Context} :
      Typing Γ Ty.string →
      Typing Γ Ty.number
  
  | «let»
      {Γ : Context} {τ₁ τ₂ : Ty}:
      Typing Γ τ₁ →
      Typing (τ₁ :: Γ) τ₂ →
      Typing Γ τ₂
  deriving DecidableEq, Repr

notation:40 Γ " ⊢ " τ => Typing Γ τ
notation:40 "⊢ " τ => Typing [] τ
