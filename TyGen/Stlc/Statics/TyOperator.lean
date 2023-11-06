import Stlc.Statics.Ty

namespace Statics

inductive TyOperator where
  | var
  | unit
  | prod : TyOperator → TyOperator → TyOperator
  | void
  | sum : TyOperator → TyOperator → TyOperator
  | arrow : Ty → TyOperator → TyOperator
  deriving DecidableEq, Repr

namespace TyOperator

inductive Subst (τ : Ty) : TyOperator → Ty → Type where
  | var : Subst τ TyOperator.var τ
  | unit : Subst τ TyOperator.unit Ty.unit
  | prod
      {τₗ' τᵣ' : Ty} {τ_opₗ τ_opᵣ : TyOperator} :
      Subst τ τ_opₗ τₗ' →
      Subst τ τ_opᵣ τᵣ' →
      Subst τ (TyOperator.prod τ_opₗ τ_opᵣ) (Ty.prod τₗ' τᵣ')
  | void : Subst τ TyOperator.void Ty.void
  | sum
      {τₗ' τᵣ' : Ty} {τ_opₗ τ_opᵣ : TyOperator} :
      Subst τ τ_opₗ τₗ' →
      Subst τ τ_opᵣ τᵣ' →
      Subst τ (TyOperator.sum τ_opₗ τ_opᵣ) (Ty.sum τₗ' τᵣ')
  | arrow
      {τ₁ τ₂ : Ty} {τ_op₂ : TyOperator} :
      Subst τ τ_op₂ τ₂ →
      Subst τ (TyOperator.arrow τ₁ τ_op₂) (Ty.arrow τ₁ τ₂)
  deriving DecidableEq, Repr

def infer (τ_op : TyOperator) (τ : Ty) : Σ τ' : Ty, Subst τ τ_op τ' :=
  match τ_op with
  | .var => ⟨_, Subst.var⟩
  | .unit => ⟨_, Subst.unit⟩
  | .prod τ_opₗ τ_opᵣ => ⟨_, Subst.prod (τ_opₗ.infer τ).2 (τ_opᵣ.infer τ).2⟩
  | .void => ⟨_, Subst.void⟩
  | .sum τ_opₗ τ_opᵣ => ⟨_, Subst.sum (τ_opₗ.infer τ).2 (τ_opᵣ.infer τ).2⟩
  | .arrow _ τ_op₂ => ⟨_, Subst.arrow (τ_op₂.infer τ).2⟩

theorem infer_sound {τ τ' : Ty} {τ_op: TyOperator} : (s : Subst τ τ_op τ') → τ_op.infer τ = ⟨τ', s⟩
  | .var | .unit | .void => rfl
  | .prod sₗ sᵣ => by simp [infer]; rw [infer_sound sₗ, infer_sound sᵣ]
  | .sum sₗ sᵣ => by simp [infer]; rw [infer_sound sₗ, infer_sound sᵣ]
  | .arrow s₂ => by simp [infer]; rw [infer_sound s₂]

end TyOperator
