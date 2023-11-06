import Stlc.Statics.Context
import Stlc.Statics.Expr.Core
import Stlc.Statics.Expr.Rename
import Stlc.Statics.Ty
import Stlc.Statics.VarIn

namespace Statics

abbrev Subst (Γ Γ' : Context) : Type := ∀ {τ : Ty}, (Γ ∋ τ) → Γ' ⊢ τ

abbrev ClosingSubst (Γ : Context) : Type := Subst Γ []

namespace Subst

def exts {Γ Γ' : Context} {τ : Ty} (σ : Subst Γ Γ') : Subst (τ :: Γ) (τ :: Γ')
  | _, .here => Expr.var VarIn.here
  | _, .there a => Expr.rename VarIn.there (σ a)

def extsᵣ {Γ Γ' : Context} (σ : Subst Γ Γ') : (τs : List Ty) → Subst (τs ++ Γ) (τs ++ Γ')
  | [], _ => σ
  | _ :: τs, _ => exts (extsᵣ σ τs)

def zero {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) : Subst (τ :: Γ) Γ
  | _, .here => e
  | _, .there a => Expr.var a

end Subst

def Expr.subst {Γ Γ' : Context} {τ : Ty} (σ : Subst Γ Γ') : (Γ ⊢ τ) → Γ' ⊢ τ
  | .var a => σ a
  | .triv => Expr.triv
  | .pair e₁ e₂ => Expr.pair (e₁.subst σ) (e₂.subst σ)
  | .projₗ e => Expr.projₗ (e.subst σ)
  | .projᵣ e => Expr.projᵣ (e.subst σ)
  | .nullary_case e => Expr.nullary_case (e.subst σ)
  | .inₗ eₗ => Expr.inₗ (eₗ.subst σ)
  | .inᵣ eᵣ => Expr.inᵣ (eᵣ.subst σ)
  | .binary_case e eₗ eᵣ => Expr.binary_case (e.subst σ) (eₗ.subst σ.exts) (eᵣ.subst σ.exts)
  | .generic_ext τ_op s s' e' e => Expr.generic_ext τ_op s s' (e'.subst σ.exts) (e.subst σ)
  | .abstraction e => Expr.abstraction (e.subst σ.exts)
  | .application e₁ e₂ => Expr.application (e₁.subst σ) (e₂.subst σ)

notation:100 "⟪ " s " ⟫" => Expr.subst s

namespace Expr

abbrev subst_zero {Γ : Context} {τ τ' : Ty} (e : Γ ⊢ τ) (e' : (τ :: Γ) ⊢ τ') : Γ ⊢ τ' := (⟪ Subst.zero e ⟫) e'

notation:100 e " [ " e' " ]" => subst_zero e' e

end Expr

namespace Subst

abbrev ids {Γ : Context} : Subst Γ Γ := Expr.var

abbrev shift {Γ : Context} {τ : Ty} : Subst Γ (τ :: Γ) := Expr.var ∘ VarIn.there

notation:40 "↑" => shift

def cons {Γ Γ' : Context} {τ : Ty} (e : Γ' ⊢ τ) (σ : Subst Γ Γ') : Subst (τ :: Γ) Γ'
  | _, .here => e
  | _, .there a => σ a

infixr:60 " •` " => cons

abbrev seq {Γ Γ' Γ'' : Context} (σ : Subst Γ Γ') (σ' : Subst Γ' Γ'') : Subst Γ Γ'' := ⟪ σ' ⟫ ∘ σ

infixr:50 " ; " => seq

end Subst

-- Relating original definitions to σ-algebra

namespace Rename

abbrev subst {Γ Γ' : Context} (ρ : Rename Γ Γ') : Subst Γ Γ' := Subst.ids ∘ ρ

@[simp]
theorem subst_ids {Γ : Context} : @Eq (Subst Γ Γ) ids.subst Subst.ids := rfl

@[simp]
theorem subst_comp
  {Γ Γ' Γ'' : Context}
  (ρ : Rename Γ Γ') (ρ' : Rename Γ' Γ'') :
  @Eq (Subst Γ Γ'') (subst (ρ' ∘ ρ)) (ρ.subst ; ρ'.subst) := rfl

@[simp]
theorem subst_ext
  {Γ Γ' : Context} {τ : Ty}
  (ρ : Rename Γ Γ') :
  @Eq (Subst (τ :: Γ) (τ :: Γ')) (subst ρ.ext) (Subst.exts ρ.subst)
:=
  let lem {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → subst ρ.ext a = Subst.exts ρ.subst a
  | .here => rfl
  | .there a => rfl

  funext (λ _ => funext lem)

@[simp]
theorem subst_shift {Γ : Context} {τ : Ty} : @Eq (Subst Γ (τ :: Γ)) shift.subst Subst.shift := rfl

@[simp]
theorem subst_swap
  {Γ : Context} {τ τ' : Ty} :
  @Eq (Subst (τ' :: τ :: Γ) (τ :: τ' :: Γ)) swap.subst ((Expr.var (VarIn.there VarIn.here)) •` (Expr.var VarIn.here) •` ((↑) ; (↑) ; Subst.ids))
:=
  let lem : {τ'' : Ty} → (a : (τ' :: τ :: Γ) ∋ τ'') → swap.subst a = ((Expr.var (VarIn.there VarIn.here)) •` (Expr.var VarIn.here) •` ((↑) ; (↑) ; Subst.ids)) a
  | _, .here => rfl
  | _, .there .here => rfl
  | _, .there (.there a) => by rfl

  funext (λ _ => funext lem)

theorem rename_subst_subst_arg {Γ Γ' : Context} (ρ : Rename Γ Γ') {τ : Ty} : (e : Γ ⊢ τ) → e.rename ρ = (⟪ ρ.subst ⟫) e
  | .var _ | .triv => rfl
  | .pair e₁ e₂ => by simp only [Expr.rename, Expr.subst, rename_subst_subst_arg ρ e₁, rename_subst_subst_arg ρ e₂]
  | .projₗ e | .projᵣ e => by simp only [Expr.rename, Expr.subst, rename_subst_subst_arg ρ e]
  | .nullary_case e => by simp only [Expr.rename, Expr.subst, rename_subst_subst_arg ρ e]
  | .inₗ eₗ => by simp only [Expr.rename, Expr.subst, rename_subst_subst_arg ρ eₗ]
  | .inᵣ eᵣ => by simp only [Expr.rename, Expr.subst, rename_subst_subst_arg ρ eᵣ]
  | .binary_case e eₗ eᵣ => by
      simp only [
        Expr.rename, Expr.subst, rename_subst_subst_arg ρ e, rename_subst_subst_arg ρ.ext eₗ,
        rename_subst_subst_arg ρ.ext eᵣ, subst_ext
      ]
  | .generic_ext τ_op s s' e' e => by
      simp only [Expr.rename, Expr.subst, rename_subst_subst_arg ρ.ext e', rename_subst_subst_arg ρ e, subst_ext]
  | .abstraction e => by simp only [Expr.rename, Expr.subst, rename_subst_subst_arg ρ.ext e, subst_ext]
  | .application e₁ e₂ => by simp only [Expr.rename, Expr.subst, rename_subst_subst_arg ρ e₁, rename_subst_subst_arg ρ e₂]

@[simp]
theorem rename_subst_subst {Γ Γ' : Context} {τ : Ty} (ρ : Rename Γ Γ') : @Expr.rename _ _ τ ρ = (⟪ subst ρ ⟫) :=
  funext (rename_subst_subst_arg ρ)

end Rename

namespace Subst

@[simp]
theorem exts_cons_shift
  {Γ Γ' : Context} {τ : Ty}
  (σ : Subst Γ Γ') :
  @Eq (Subst (τ :: Γ) (τ :: Γ')) (exts σ) (((Expr.var VarIn.here) •` (σ ; (↑))))
:=
  let lem {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → exts σ a = ((Expr.var VarIn.here) •` (σ ; (↑))) a
  | .here => rfl
  | .there _ => by simp [exts, Expr.shift]; rfl

  funext (λ _ => funext lem)

@[simp]
theorem subst_zero_cons_ids {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) : @Eq (Subst (τ :: Γ) Γ) (zero e) (e •` ids) :=
  let lem : {τ' : Ty} → (a : (τ :: Γ) ∋ τ') → (zero e) a = (e •` ids) a
  | _, .here => rfl
  | _, .there _ => rfl

  funext (λ _ => funext lem)

end Subst

-- Rewrite system

namespace Subst

@[simp]
theorem subst_head {Γ Γ' : Context} {τ : Ty} (σ : Subst Γ Γ') (e : Γ' ⊢ τ) : (⟪ e •` σ ⟫) (Expr.var VarIn.here) = e := rfl

@[simp]
theorem subst_tail {Γ Γ' : Context} {τ : Ty} (σ : Subst Γ Γ') (e : Γ' ⊢ τ) : @Eq (Subst Γ Γ') ((↑) ; e •` σ) σ := rfl

@[simp]
theorem subst_η
  {Γ Γ' : Context} {τ : Ty}
  (σ : Subst (τ :: Γ) Γ') :
  @Eq (Subst (τ :: Γ) Γ') ((⟪ σ ⟫) (Expr.var VarIn.here) •` ((↑) ; σ)) σ
:=
  let lem {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → ((⟪ σ ⟫) (Expr.var VarIn.here) •` ((↑) ; σ)) a = σ a
  | .here => rfl
  | .there _ => rfl

  funext (λ _ => funext lem)

@[simp]
theorem zero_shift {Γ : Context} {τ : Ty} : @Eq (Subst (τ :: Γ) (τ :: Γ)) ((Expr.var VarIn.here) •` (↑)) ids :=
  let lem {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → ((Expr.var VarIn.here) •` (↑)) a = ids a
  | .here => rfl
  | .there _ => rfl

  funext (λ _ => funext lem)

@[simp]
theorem subst_id_left {Γ Γ' : Context} (σ : Subst Γ Γ') : @Eq (Subst Γ Γ') (ids ; σ) σ := rfl

theorem subst_id_arg {Γ : Context} {τ : Ty} : (e : Γ ⊢ τ) → @Eq (Γ ⊢ τ) ((⟪ ids ⟫) e) e
  | .var _ | .triv => rfl
  | .pair e₁ e₂ => by simp only [Expr.subst, subst_id_arg e₁, subst_id_arg e₂, id_eq]
  | .projₗ e | .projᵣ e => by simp only [Expr.subst, subst_id_arg e, id_eq]
  | .nullary_case e => by simp only [Expr.subst, subst_id_arg e]
  | .inₗ eₗ => by simp only [Expr.subst, subst_id_arg eₗ]
  | .inᵣ eᵣ => by simp only [Expr.subst, subst_id_arg eᵣ]
  | .binary_case e eₗ eᵣ => by
      simp only [
        Expr.subst, subst_id_arg e, subst_id_arg eₗ, subst_id_arg eᵣ,
        exts_cons_shift, subst_id_left, zero_shift
      ]
  | .generic_ext τ_op s s' e' e => by
      simp only [Expr.subst, subst_id_arg e', subst_id_arg e, exts_cons_shift, subst_id_left, zero_shift]
  | .abstraction e => by simp only [Expr.subst, subst_id_arg e, exts_cons_shift, subst_id_left, zero_shift]
  | .application e₁ e₂ => by simp only [Expr.subst, subst_id_arg e₁, subst_id_arg e₂]

@[simp]
theorem subst_id {Γ : Context} {τ : Ty} : @Eq ((Γ ⊢ τ) → Γ ⊢ τ) (⟪ ids ⟫ ) id :=
  funext subst_id_arg

@[simp]
theorem subst_id_right {Γ Γ' : Context} (σ : Subst Γ Γ') : @Eq (Subst Γ Γ') (σ ; ids) σ :=
  let lem {τ' : Ty} : (a : Γ ∋ τ') → (σ ; ids) a = σ a
  := by
    simp only [Function.comp_apply, subst_id, id_eq, implies_true]

  funext (λ _ => funext lem)

@[simp]
theorem subst_pair
  {Γ Γ' : Context} {τ : Ty}
  (σ : Subst Γ Γ')
  (e₁ : Γ ⊢ τ)
  (e₂ : Γ ⊢ τ) :
  (⟪ σ ⟫) (Expr.pair e₁ e₂) = (Expr.pair ((⟪ σ ⟫) e₁) ((⟪ σ ⟫) e₂))
:=
  rfl

@[simp]
theorem subst_projₗ
  {Γ Γ' : Context} {τ₁ τ₂ : Ty}
  (σ : Subst Γ Γ')
  (e : Γ ⊢ Ty.prod τ₁ τ₂) :
  (⟪ σ ⟫) (Expr.projₗ e) = (Expr.projₗ ((⟪ σ ⟫) e))
:=
  rfl

@[simp]
theorem subst_projᵣ
  {Γ Γ' : Context} {τ₁ τ₂ : Ty}
  (σ : Subst Γ Γ')
  (e : Γ ⊢ Ty.prod τ₁ τ₂) :
  (⟪ σ ⟫) (Expr.projᵣ e) = (Expr.projᵣ ((⟪ σ ⟫) e))
:=
  rfl

@[simp]
theorem subst_nullary_case
  {Γ Γ' : Context} {τ : Ty}
  (σ : Subst Γ Γ')
  (e : Γ ⊢ Ty.void) :
  (⟪ σ ⟫) (Expr.nullary_case e : Γ ⊢ τ) = Expr.nullary_case ((⟪ σ ⟫) e)
:=
  rfl

@[simp]
theorem subst_inₗ
  {Γ Γ' : Context} {τₗ τᵣ : Ty}
  (σ : Subst Γ Γ')
  (eₗ : Γ ⊢ τₗ) :
  (⟪ σ ⟫) (Expr.inₗ eₗ : Γ ⊢ Ty.sum τₗ τᵣ) = Expr.inₗ ((⟪ σ ⟫) eₗ)
:=
  rfl

@[simp]
theorem subst_inr
  {Γ Γ' : Context} {τₗ τᵣ : Ty}
  (σ : Subst Γ Γ')
  (eᵣ : Γ ⊢ τᵣ) :
  (⟪ σ ⟫) (Expr.inᵣ eᵣ : Γ ⊢ Ty.sum τₗ τᵣ) = Expr.inᵣ ((⟪ σ ⟫) eᵣ)
:= by
  simp only [Expr.subst]

@[simp]
theorem subst_binary_case
  {Γ Γ' : Context} {τ τₗ τᵣ : Ty}
  (σ : Subst Γ Γ')
  (e : Γ ⊢ Ty.sum τₗ τᵣ) (eₗ : (τₗ :: Γ) ⊢ τ) (eᵣ : (τᵣ :: Γ) ⊢ τ) :
  (⟪ σ ⟫) (Expr.binary_case e eₗ eᵣ) = Expr.binary_case ((⟪ σ ⟫) e) ((⟪ σ.exts ⟫) eₗ) ((⟪ σ.exts ⟫) eᵣ)
:= by
  simp only [Expr.subst]

@[simp]
theorem subst_generic_ext
  {Γ Γ' : Context} {ρ ρ' τ_in τ_out : Ty}
  (σ : Subst Γ Γ') (τ_op : TyOperator) (s : TyOperator.Subst ρ τ_op τ_in) (s' : TyOperator.Subst ρ' τ_op τ_out)
  (e' : (ρ :: Γ) ⊢ ρ') (e : Γ ⊢ τ_in) :
  (⟪ σ ⟫) (Expr.generic_ext τ_op s s' e' e) = Expr.generic_ext τ_op s s' ((⟪ σ.exts ⟫) e') ((⟪ σ ⟫) e)
:=
  rfl

@[simp]
theorem subst_abstraction
  {Γ Γ' : Context} {τ τ' : Ty}
  (σ : Subst Γ Γ')
  (e : τ :: Γ ⊢ τ') :
  (⟪ σ ⟫) (Expr.abstraction e) = Expr.abstraction ((⟪ σ.exts ⟫) e)
:=
  rfl

@[simp]
theorem subst_application
  {Γ Γ' : Context} {τ τ' : Ty}
  (σ : Subst Γ Γ')
  (e₁ : Γ ⊢ Ty.arrow τ τ') (e₂ : Γ ⊢ τ) :
  (⟪ σ ⟫) (Expr.application e₁ e₂) = Expr.application ((⟪ σ ⟫) e₁) ((⟪ σ ⟫) e₂)
:=
  rfl

@[simp]
theorem subst_dist
  {Γ Γ' Γ'' : Context} {τ : Ty}
  (σ : Subst Γ Γ') (σ' : Subst Γ' Γ'')
  (e : Γ' ⊢ τ) :
  @Eq (Subst (τ :: Γ) Γ'') ((e •` σ) ; σ') ((⟪ σ' ⟫) e •` (σ ; σ'))
:=
  let lem {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → ((e •` σ) ; σ') a = ((⟪ σ' ⟫) e •` (σ ; σ')) a
  | .here => rfl
  | .there _ => rfl

  funext (λ _ => funext lem)

theorem subst_shift_commuteᵣ
  {Γ Γ' : Context} {τ τ' : Ty} {σ : Subst Γ Γ'}
  (τs : List Ty) (e : τs ++ Γ ⊢ τ) :
  @Eq (τs ++ τ' :: Γ' ⊢ τ) ((⟪ Subst.extsᵣ σ.exts τs ⟫) (e.rename (Rename.extᵣ Rename.shift τs)))
                           (((⟪ Subst.extsᵣ σ τs ⟫) e).rename (Rename.extᵣ Rename.shift τs))
:=
  match τ, e with
  | τ, .var a => by
      let rec lem
        {Γ Γ' : Context} {τ τ' : Ty} {σ : Subst Γ Γ'}
        (τs : List Ty) (a : τs ++ Γ ∋ τ):
        @Eq (τs ++ τ' :: Γ' ⊢ τ) (extsᵣ σ.exts τs (Rename.extᵣ Rename.shift τs a))
                                 ((extsᵣ σ τs a).rename (Rename.extᵣ Rename.shift τs)) := by
          match τs, a with
          | [], _ => rfl
          | _ :: _, .here => rfl
          | _ :: τs, .there a =>
              simp only [Rename.extᵣ, Subst.extsᵣ, id]
              conv => lhs; dsimp only [Rename.ext]
              generalize h : (extsᵣ σ.exts τs : {τ : Ty} → (τs ++ τ' :: Γ ∋ τ) → τs ++ τ' :: Γ' ⊢ τ) = tmp
              dsimp only [Subst.exts]
              rw [← h]
              conv => rhs; dsimp only [Subst.exts]
              simp only [
                Expr.rename_comp_arg Rename.shift (Rename.ext (Rename.extᵣ Rename.shift τs)),
                Rename.shift_commute,
                ← Expr.rename_comp_arg (Rename.extᵣ Rename.shift τs) Rename.shift,
                ← @lem Γ Γ' τ τ' σ τs a
              ]

      dsimp only [Expr.rename, Expr.subst]
      exact lem τs a
  | _, .triv => rfl
  | _, .pair e₁ e₂ => by
      rename_i τ₁ τ₂
      simp only [Expr.rename, Expr.subst, subst_shift_commuteᵣ τs e₁, subst_shift_commuteᵣ τs e₂]
  | _, .projₗ e | _, .projᵣ e => by simp only [Expr.rename, Expr.subst, subst_shift_commuteᵣ τs e]
  | _, .nullary_case e => by simp only [Expr.rename, Expr.subst, subst_shift_commuteᵣ τs e]
  | _, .inₗ eₗ => by simp only [Expr.rename, Expr.subst, subst_shift_commuteᵣ τs eₗ]
  | _, .inᵣ eᵣ => by simp only [Expr.rename, Expr.subst, subst_shift_commuteᵣ τs eᵣ]
  | _, .binary_case e eₗ eᵣ => by
      rename_i τ τₗ τᵣ
      simp only [Expr.rename, Expr.subst, subst_shift_commuteᵣ τs e]
      have := @subst_shift_commuteᵣ _ _ τ τ' σ (τₗ :: τs) eₗ
      have := @subst_shift_commuteᵣ _ _ τ τ' σ (τᵣ :: τs) eᵣ
      congr
  | _, .generic_ext τ_op s s' e' e => by
      rename_i τ_out ρ ρ' τ_in
      simp only [Expr.rename, Expr.subst, subst_shift_commuteᵣ τs e]
      have := @subst_shift_commuteᵣ _ _ ρ' τ' σ (ρ :: τs) e'
      congr
  | _, .abstraction e => by
      rename_i τ₁ τ₂
      simp only [Expr.rename, Expr.subst]
      have := @subst_shift_commuteᵣ _ _ τ₂ τ' σ (τ₁ :: τs) e
      congr
  | _, .application e₁ e₂ => by simp only [Expr.rename, Expr.subst, subst_shift_commuteᵣ τs e₁, subst_shift_commuteᵣ τs e₂]

theorem subst_shift_commute
  {Γ Γ' : Context} {τ τ' : Ty} {σ : Subst Γ Γ'}
  (e : Γ ⊢ τ) :
  @Eq (τ' :: Γ' ⊢ τ) ((⟪ σ.exts ⟫) e.shift) ((⟪ σ ⟫) e).shift
:= by
  let h := @subst_shift_commuteᵣ Γ Γ' τ τ' σ [] e
  simp only [Subst.extsᵣ, Rename.extᵣ, id] at h
  exact h

theorem exts_seq_dist
  {Γ Γ' Γ'' : Context} {τ : Ty}
  (σ : Subst Γ Γ') (σ' : Subst Γ' Γ'') :
  @Eq (Subst (τ :: Γ) (τ :: Γ'')) (σ.exts ; σ'.exts) (exts (σ ; σ'))
:=
  let lem {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → (σ.exts ; σ'.exts) a = exts (σ ; σ') a
  | .here => rfl
  | .there a => by
      calc (σ.exts ; σ'.exts) (VarIn.there a)
        _ = (⟪ σ'.exts ⟫) (σ a).shift := by rfl
        _ = Expr.shift ((⟪ σ' ⟫) (σ a)) := by exact subst_shift_commute (σ a)
        _ = _ := rfl

  funext (λ _ => funext lem)

theorem extsᵣ_seq_dist
  {Γ Γ' Γ'' : Context}
  (σ : Subst Γ Γ') (σ' : Subst Γ' Γ'') :
  (τs : List Ty) →
  @Eq (Subst (τs ++ Γ) (τs ++ Γ'')) (extsᵣ σ τs ; extsᵣ σ' τs) (extsᵣ (σ ; σ') τs)
  | [] => rfl
  | τ :: τs => by
      simp only [extsᵣ, id_eq]
      rw [exts_seq_dist, extsᵣ_seq_dist σ σ' τs]

@[simp]
theorem subst_subst
  {Γ Γ' Γ'' : Context} {τ : Ty}
  (σ : Subst Γ Γ') (σ' : Subst Γ' Γ'') :
  (e : Γ ⊢ τ) →
  (⟪ σ' ⟫) ((⟪ σ ⟫) e) = (⟪ σ ; σ' ⟫) e
  | .var _ | .triv => rfl
  | .pair e₁ e₂ => by simp only [Expr.subst, subst_subst σ σ' e₁, subst_subst σ σ' e₂]
  | .projₗ e | .projᵣ e => by simp only [Expr.subst, subst_subst σ σ' e]
  | .nullary_case e => by simp only [Expr.subst, subst_subst σ σ' e]
  | .inₗ eₗ => by simp only [Expr.subst, subst_subst σ σ' eₗ]
  | .inᵣ eᵣ => by simp only [Expr.subst, subst_subst σ σ' eᵣ]
  | .binary_case e eₗ eᵣ => by
      simp only [
        Expr.subst, subst_subst σ σ' e, subst_subst σ.exts σ'.exts eₗ,
        subst_subst σ.exts σ'.exts eᵣ, exts_seq_dist σ σ'
      ]
  | .generic_ext τ_op h_in h_out e' e => by
      simp only [Expr.subst, subst_subst σ.exts σ'.exts e', subst_subst σ σ' e, exts_seq_dist σ σ']
  | .abstraction e => by simp only [Expr.subst, subst_subst σ.exts σ'.exts e, exts_seq_dist σ σ']
  | .application e₁ e₂ => by simp only [Expr.subst, subst_subst σ σ' e₁, subst_subst σ σ' e₂]

@[simp]
theorem subst_assoc
  {Γ Γ' Γ'' Γ''' : Context}
  (σ : Subst Γ Γ') (σ' : Subst Γ' Γ'') (σ'' : Subst Γ'' Γ''') :
  @Eq (Subst Γ Γ''') ((σ ; σ') ; σ'') (σ ; (σ' ; σ''))
:=
  let lem {τ : Ty} : (a : Γ ∋ τ) → ((σ ; σ') ; σ'') a = (σ ; (σ' ; σ'')) a := by simp

  funext (λ _ => funext lem)

theorem subst_commute
  {Γ Γ' : Context} {τ τ' : Ty}
  (σ : Subst Γ Γ') (e : (τ :: Γ) ⊢ τ') (e' : Γ ⊢ τ) :
  ((⟪ exts σ ⟫) e) [ (⟪ σ ⟫) e' ] = (⟪ σ ⟫) (e [ e' ])
:= by
  simp only [
    exts_cons_shift, subst_subst, subst_zero_cons_ids, subst_dist, subst_head, subst_assoc, subst_tail,
    subst_id_right, subst_id_left
  ]

end Subst
