import Aesop

namespace Statics

inductive Ty where
  | nat
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr

namespace Ty

abbrev arrowᵣ (τ : Ty) (tys : List Ty) : Ty := List.foldr (λ τ' τ => Ty.arrow τ' τ) τ tys

@[simp]
theorem arrowᵣ_arrow_comm
  (τ τ' : Ty) :
  (tys : List Ty) →
  arrowᵣ (Ty.arrow τ τ') tys = arrowᵣ τ' (tys ++ [τ])
  | [] => rfl
  | ty :: tys => by simp only [List.append_eq, List.cons_append, List.foldr_append, List.foldr]

end Ty
