import Stlc.Statics.Context
import Stlc.Statics.Expr.Core
import Stlc.Statics.Ty
import Stlc.Statics.VarIn

namespace Statics

abbrev Rename (Γ Γ' : Context) : Type := ∀ {τ : Ty}, (Γ ∋ τ) → Γ' ∋ τ

namespace Rename

abbrev ids {Γ : Context} : Rename Γ Γ := id

def ext {Γ Γ' : Context} {τ : Ty} (ρ : Rename Γ Γ') : Rename (τ :: Γ) (τ :: Γ')
  | _, .here => VarIn.here
  | _, .there a => VarIn.there (ρ a)

@[simp]
theorem ext_comp
  {Γ Γ' Γ'' : Context} {τ : Ty}
  (ρ : Rename Γ Γ') (ρ' : Rename Γ' Γ'') :
  @Eq (Rename (τ :: Γ) (τ :: Γ'')) (ext (ρ' ∘ ρ)) (ρ'.ext ∘ ρ.ext)
:=
  let lem {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → ext (ρ' ∘ ρ) a = (ρ'.ext ∘ ρ.ext) a
  | .here => rfl
  | .there _ => rfl

  funext (fun _ => funext lem)

def extᵣ {Γ Γ' : Context} (ρ : Rename Γ Γ') : (τs : List Ty) → Rename (τs ++ Γ) (τs ++ Γ')
  | [], _ => ρ
  | _ :: τs, _ => ext (ρ.extᵣ τs)

abbrev shift {Γ : Context} {τ : Ty} : Rename Γ (τ :: Γ) := VarIn.there

@[simp]
theorem shift_commute
  {Γ Γ' : Context} {τ : Ty}
  (ρ : Rename Γ Γ') :
  @Eq (Rename Γ (τ :: Γ')) (ρ.ext ∘ shift) (shift ∘ ρ)
:=
  let lem {τ' : Ty} (a : (Γ ∋ τ')) : @Eq (τ :: Γ' ∋ τ') ((ρ.ext ∘ shift) a) ((shift ∘ ρ) a) := rfl

  funext (fun _ => funext lem)

def swap {Γ : Context} {τ τ' : Ty} : Rename (τ' :: τ :: Γ) (τ :: τ' :: Γ)
  | _, .here => VarIn.there VarIn.here
  | _, .there .here => VarIn.here
  | _, .there (.there a) => VarIn.there (VarIn.there a)

@[simp]
theorem shift_swap
  {Γ : Context} {τ τ' : Ty} :
  @Eq (Rename (τ :: Γ) (τ :: τ' :: Γ)) (swap ∘ shift) shift.ext
:=
  let lem {τ'' : Ty} : (a : (τ :: Γ) ∋ τ'') →@Eq (τ :: τ' :: Γ ∋ τ'') ((swap ∘ shift) a) (shift.ext a)
    | .here => rfl
    | .there a => rfl

  funext (fun _ => funext lem)

end Rename

def Expr.rename {Γ Γ' : Context} {τ : Ty} (ρ : Rename Γ Γ') : (Γ ⊢ τ) → Γ' ⊢ τ
  | .var a => Expr.var (ρ a)
  | .triv => Expr.triv
  | .pair e₁ e₂ => Expr.pair (e₁.rename ρ) (e₂.rename ρ)
  | .projₗ e => Expr.projₗ (e.rename ρ)
  | .projᵣ e => Expr.projᵣ (e.rename ρ)
  | .nullary_case e => Expr.nullary_case (e.rename ρ)
  | .inₗ eₗ => Expr.inₗ (eₗ.rename ρ)
  | .inᵣ eᵣ => Expr.inᵣ (eᵣ.rename ρ)
  | .binary_case e eₗ eᵣ => Expr.binary_case (e.rename ρ) (eₗ.rename ρ.ext) (eᵣ.rename ρ.ext)
  | .generic_ext τ_op s s' e' e => Expr.generic_ext τ_op s s' (e'.rename ρ.ext) (e.rename ρ)
  | .abstraction e => Expr.abstraction (e.rename ρ.ext)
  | .application e₁ e₂ => Expr.application (e₁.rename ρ) (e₂.rename ρ)

theorem Expr.rename_comp_arg
  {Γ Γ' Γ'' : Context} {τ : Ty}
  (ρ : Rename Γ Γ') (ρ' : Rename Γ' Γ'') : 
  (e : Γ ⊢ τ) →
  (e.rename ρ).rename ρ' = e.rename (ρ' ∘ ρ)
  | .var _ | triv => rfl
  | .pair e₁ e₂ => by simp only [rename, rename_comp_arg ρ ρ' e₁, rename_comp_arg ρ ρ' e₂]
  | .projₗ e | .projᵣ e => by simp only [rename, rename_comp_arg ρ ρ' e]
  | .nullary_case e => by simp only [Expr.rename, Expr.rename_comp_arg ρ ρ' e]
  | .inₗ eₗ => by simp only [Expr.rename, Expr.rename_comp_arg ρ ρ' eₗ]
  | .inᵣ eᵣ => by simp only [Expr.rename, Expr.rename_comp_arg ρ ρ' eᵣ]
  | .binary_case e eₗ eᵣ => by
      simp only [
        Expr.rename, Expr.rename_comp_arg ρ ρ' e,
        Expr.rename_comp_arg ρ.ext ρ'.ext eₗ, Expr.rename_comp_arg ρ.ext ρ'.ext eᵣ,
        Rename.ext_comp
      ]
  | .generic_ext τ_op s s' e' e => by
      simp only [Expr.rename, Expr.rename_comp_arg ρ.ext ρ'.ext e', Expr.rename_comp_arg ρ ρ' e, Rename.ext_comp]
  | .abstraction e => by simp only [Expr.rename, Expr.rename_comp_arg ρ.ext ρ'.ext e, Rename.ext_comp]
  | .application e₁ e₂ => by simp only [Expr.rename, Expr.rename_comp_arg ρ ρ' e₁, Expr.rename_comp_arg ρ ρ' e₂]

@[simp]
theorem Expr.rename_comp
  {Γ Γ' Γ'' : Context} {τ : Ty}
  (ρ : Rename Γ Γ') (ρ' : Rename Γ' Γ'') : 
  @Eq ((Γ ⊢ τ) → Γ'' ⊢ τ) (rename ρ' ∘ rename ρ) (rename (ρ' ∘ ρ))
:=
  funext (Expr.rename_comp_arg ρ ρ')

namespace Expr

abbrev shift {Γ : Context} {τ τ' : Ty} (e : Γ ⊢ τ') : (τ :: Γ) ⊢ τ' := e.rename Rename.shift

abbrev swap {Γ : Context} {τ τ' τ'' : Ty} (e : (τ' :: τ :: Γ) ⊢ τ'') : (τ :: τ' :: Γ) ⊢ τ'' := e.rename Rename.swap

end Expr
