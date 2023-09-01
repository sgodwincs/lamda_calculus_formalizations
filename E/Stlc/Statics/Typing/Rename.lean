import Stlc.Statics.Any
import Stlc.Statics.Context
import Stlc.Statics.Ty
import Stlc.Statics.Typing.Core

namespace Statics

abbrev Rename (Γ : Context) (Δ : Context) : Type := ∀ {τ : Ty}, (Γ ∋ τ) → (Δ ∋ τ)

namespace Rename

abbrev ids {Γ : Context} : Rename Γ Γ := id

def ext
  {Γ Δ : Context} {τ : Ty}
  (ρ : Rename Γ Δ) :
  Rename (τ :: Γ) (τ :: Δ)
  | _, .here => Any.here
  | _, .there a => Any.there (ρ a)

@[simp]
theorem ext_comp
  {Γ Δ Ψ : Context} {τ : Ty}
  (ρ : Rename Γ Δ) (ρ' : Rename Δ Ψ) :
  @Eq (Rename (τ :: Γ) (τ :: Ψ)) (ext (ρ' ∘ ρ)) (ext ρ' ∘ ext ρ) :=
  let lemma {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → ext (ρ' ∘ ρ) a = (ext ρ' ∘ ext ρ) a
  | .here => rfl
  | .there _ => rfl

  funext (fun _ => funext lemma)

def extᵣ
  {Γ Δ : Context}
  (ρ : Rename Γ Δ) :
  (tys : List Ty) → Rename (tys ++ Γ) (tys ++ Δ)
  | .nil, _ => by simp only [List.nil_append]; exact ρ
  | τ :: tys, _ => by
      simp only [List.cons_append]
      exact ext (extᵣ ρ tys)

abbrev shift {Γ : Context} {τ : Ty} : Rename Γ (τ :: Γ) := Any.there

@[simp]
theorem shift_commute
  {Γ Δ : Context} {τ : Ty}
  (ρ : Rename Γ Δ) :
  @Eq (Rename Γ (τ :: Δ)) ((ext ρ) ∘ shift) (shift ∘ ρ) :=
  let lemma
    {τ' : Ty} (a : (Γ ∋ τ')) :
    @Eq (τ :: Δ ∋ τ') (((ext ρ) ∘ shift) a) ((shift ∘ ρ) a) := rfl

  funext (fun _ => funext lemma)

def swap {Γ : Context} {τ₁ τ₂ : Ty} : Rename (τ₂ :: τ₁ :: Γ) (τ₁ :: τ₂ :: Γ)
  | _, .here => Any.there Any.here
  | _, .there .here => Any.here
  | _, .there (.there a) => Any.there (Any.there a)

@[simp]
theorem shift_swap
  {Γ : Context} {τ τ' : Ty} :
  @Eq (Rename (τ :: Γ) (τ :: τ' :: Γ)) (swap ∘ shift) (ext shift) :=
  let lemma
    {τ'' : Ty} :
    (a : (τ :: Γ) ∋ τ'') →
    @Eq (τ :: τ' :: Γ ∋ τ'') ((swap ∘ shift) a) (ext shift a)
    | .here => by simp only [swap, shift]; rfl
    | .there a => by simp only [swap, shift]; rfl

  funext (fun _ => funext lemma)

end Rename

namespace Typing

def rename
  {Γ Δ : Context} {τ : Ty}
  (ρ : Rename Γ Δ) :
  (Γ ⊢ τ) →
  Δ ⊢ τ
  | .var a => Typing.var (ρ a)
  | .number num => Typing.number num
  | .string s => Typing.string s
  | .plus t₁ t₂ => Typing.plus (rename ρ t₁) (rename ρ t₂)
  | .times t₁ t₂ => Typing.times (rename ρ t₁) (rename ρ t₂)
  | .concatenate t₁ t₂ => Typing.concatenate (rename ρ t₁) (rename ρ t₂)
  | .length t => Typing.length (t.rename ρ)
  | .let t₁ t₂ => Typing.let (rename ρ t₁) (rename (Rename.ext ρ) t₂)

@[simp]
theorem rename_comp_arg
  {Γ Δ Ψ : Context} {τ : Ty}
  (ρ : Rename Γ Δ) (ρ' : Rename Δ Ψ)
  (t : Γ ⊢ τ) : 
  rename ρ' (rename ρ t) = rename (ρ' ∘ ρ) t :=
  match t with
  | .var _ | .number _ | .string _ => rfl
  | .plus e₁ e₂ => by simp only [rename, rename_comp_arg ρ ρ' e₁, rename_comp_arg ρ ρ' e₂]
  | .times e₁ e₂ => by simp only [rename, rename_comp_arg ρ ρ' e₁, rename_comp_arg ρ ρ' e₂]
  | .concatenate e₁ e₂ => by simp only [rename, rename_comp_arg ρ ρ' e₁, rename_comp_arg ρ ρ' e₂]
  | .length e => by simp only [rename, rename_comp_arg ρ ρ' e]
  | .let e₁ e₂ => by simp only [rename, rename_comp_arg ρ ρ' e₁, rename_comp_arg (Rename.ext ρ) (Rename.ext ρ') e₂, Rename.ext_comp]

@[simp]
theorem rename_comp
  {Γ Δ Ψ : Context} (τ : Ty)
  (ρ : Rename Γ Δ) (ρ' : Rename Δ Ψ) :
  @Eq ((Γ ⊢ τ) → Ψ ⊢ τ) (rename ρ' ∘ rename ρ) (rename (ρ' ∘ ρ)) :=
  funext (rename_comp_arg ρ ρ')

abbrev shift
  {Γ : Context} {τ τ' : Ty}
  (t : Γ ⊢ τ') :
  (τ :: Γ) ⊢ τ' := rename Rename.shift t

abbrev swap
  {Γ : Context} {τ₁ τ₂ τ₃ : Ty}
  (t : (τ₂ :: τ₁ :: Γ) ⊢ τ₃) :
  (τ₁ :: τ₂ :: Γ) ⊢ τ₃ := rename Rename.swap t

end Typing
