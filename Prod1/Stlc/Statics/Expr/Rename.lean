import Stlc.Statics.Any
import Stlc.Statics.Context
import Stlc.Statics.Ty
import Stlc.Statics.Expr.Core

namespace Statics

abbrev Rename (Γ Δ : Context) : Type := ∀ {τ : Ty}, (Γ ∋ τ) → Δ ∋ τ

namespace Rename

abbrev ids {Γ : Context} : Rename Γ Γ := id

def ext {Γ Δ : Context} {τ : Ty} (ρ : Rename Γ Δ) : Rename (τ :: Γ) (τ :: Δ)
  | _, .here => Any.here
  | _, .there a => Any.there (ρ a)

@[simp]
theorem ext_comp
  {Γ Δ Ψ : Context} {τ : Ty}
  (ρ : Rename Γ Δ) (ρ' : Rename Δ Ψ) :
  @Eq (Rename (τ :: Γ) (τ :: Ψ)) (ext (ρ' ∘ ρ)) (ρ'.ext ∘ ρ.ext) :=
  let lemma {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → ext (ρ' ∘ ρ) a = (ρ'.ext ∘ ρ.ext) a
  | .here => rfl
  | .there _ => rfl

  funext (fun _ => funext lemma)

def extᵣ {Γ Δ : Context} (ρ : Rename Γ Δ) : (τs : List Ty) → Rename (τs ++ Γ) (τs ++ Δ)
  | [], _ => ρ
  | _ :: τs, _ => ext (ρ.extᵣ τs)

abbrev shift {Γ : Context} {τ : Ty} : Rename Γ (τ :: Γ) := Any.there

@[simp]
theorem shift_commute
  {Γ Δ : Context} {τ : Ty}
  (ρ : Rename Γ Δ) :
  @Eq (Rename Γ (τ :: Δ)) (ρ.ext ∘ shift) (shift ∘ ρ) :=
  let lemma {τ' : Ty} (a : (Γ ∋ τ')) : @Eq (τ :: Δ ∋ τ') ((ρ.ext ∘ shift) a) ((shift ∘ ρ) a) := rfl

  funext (fun _ => funext lemma)

def swap {Γ : Context} {τ τ' : Ty} : Rename (τ' :: τ :: Γ) (τ :: τ' :: Γ)
  | _, .here => Any.there Any.here
  | _, .there .here => Any.here
  | _, .there (.there a) => Any.there (Any.there a)

@[simp]
theorem shift_swap
  {Γ : Context} {τ τ' : Ty} :
  @Eq (Rename (τ :: Γ) (τ :: τ' :: Γ)) (swap ∘ shift) shift.ext :=
  let lemma
    {τ'' : Ty} :
    (a : (τ :: Γ) ∋ τ'') →
    @Eq (τ :: τ' :: Γ ∋ τ'') ((swap ∘ shift) a) (shift.ext a)
    | .here => rfl
    | .there a => rfl

  funext (fun _ => funext lemma)

end Rename

namespace Expr

def rename {Γ Δ : Context} {τ : Ty} (ρ : Rename Γ Δ) : (Γ ⊢ τ) → Δ ⊢ τ
  | .var a => Expr.var (ρ a)
  | .triv => Expr.triv
  | .pair e₁ e₂ => Expr.pair (e₁.rename ρ) (e₂.rename ρ)
  | .proj₁ e => Expr.proj₁ (e.rename ρ)
  | .proj₂ e => Expr.proj₂ (e.rename ρ)
  | .abstraction e => Expr.abstraction (e.rename ρ.ext)
  | .application e₁ e₂ => Expr.application (e₁.rename ρ) (e₂.rename ρ)

@[simp]
theorem rename_comp_arg
  {Γ Δ Ψ : Context} {τ : Ty}
  (ρ : Rename Γ Δ) (ρ' : Rename Δ Ψ) : 
  (e : Γ ⊢ τ) →
  rename ρ' (rename ρ e) = rename (ρ' ∘ ρ) e
  | .var _ | triv => rfl
  | .pair e₁ e₂ => by simp only [rename, rename_comp_arg ρ ρ' e₁, rename_comp_arg ρ ρ' e₂]
  | .proj₁ e | .proj₂ e => by simp only [rename, rename_comp_arg ρ ρ' e]
  | .abstraction e => by simp only [rename, rename_comp_arg ρ.ext ρ'.ext, Rename.ext_comp]
  | .application e₁ e₂ => by simp only [rename, rename_comp_arg ρ ρ' e₁, rename_comp_arg ρ ρ' e₂]

@[simp]
theorem rename_comp
  {Γ Δ Ψ : Context} (τ : Ty)
  (ρ : Rename Γ Δ) (ρ' : Rename Δ Ψ) :
  @Eq ((Γ ⊢ τ) → Ψ ⊢ τ) (rename ρ' ∘ rename ρ) (rename (ρ' ∘ ρ)) :=
  funext (rename_comp_arg ρ ρ')

abbrev shift {Γ : Context} {τ τ' : Ty} (e : Γ ⊢ τ') : (τ :: Γ) ⊢ τ' := e.rename Rename.shift

abbrev swap {Γ : Context} {τ τ' τ'' : Ty} (e : (τ' :: τ :: Γ) ⊢ τ'') : (τ :: τ' :: Γ) ⊢ τ'' := e.rename Rename.swap

end Expr
