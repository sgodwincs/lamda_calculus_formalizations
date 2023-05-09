import EF.Statics.Any
import EF.Statics.Context
import EF.Statics.Ty
import EF.Statics.Expr.Core
import EF.Statics.Expr.Rename

namespace Statics

abbrev Subst (Γ Δ : Context) : Type := ∀ {τ : Ty}, (Γ ∋ τ) → Δ ⊢ τ

abbrev ClosingSubst (Γ : Context) : Type := Subst Γ []

namespace Subst

def exts
  {Γ Δ : Context} {τ : Ty}
  (σ : Subst Γ Δ) :
  Subst (τ :: Γ) (τ :: Δ)
  | _, .here => Expr.var Any.here
  | _, .there a => Expr.rename Any.there (σ a)

def extsᵣ
  {Γ Δ : Context}
  (σ : Subst Γ Δ) :
  (tys : List Ty) → Subst (tys ++ Γ) (tys ++ Δ)
  | [], _ => by simp only [List.nil_append]; exact σ
  | τ :: tys, _ => by
      simp only [List.cons_append]
      exact exts (extsᵣ σ tys)

def zero {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) : Subst (τ :: Γ) Γ
  | _, .here => e
  | _, .there a => Expr.var a

end Subst

namespace Expr

def subst
  {Γ Δ : Context} {τ : Ty}
  (σ : Subst Γ Δ) :
  (Γ ⊢ τ) →
  Δ ⊢ τ
  | .var a => σ a
  | .number num => Expr.number num
  | .string s => Expr.string s
  | .abstraction e => Expr.abstraction (subst σ.exts e)
  | .application e₁ e₂ => Expr.application (subst σ e₁) (subst σ e₂)

notation:100 "⟪ " s " ⟫" => subst s

abbrev subst_zero
  {Γ : Context} {τ τ' : Ty}
  (e : Γ ⊢ τ)
  (e' : (τ :: Γ) ⊢ τ') :
  Γ ⊢ τ' := subst (Subst.zero e) e'

notation:100 e " [ " e' " ]" => subst_zero e' e

end Expr

namespace Subst

abbrev ids {Γ : Context} : Subst Γ Γ := Expr.var

abbrev shift {Γ : Context} {τ : Ty} : Subst Γ (τ :: Γ) := Expr.var ∘ Any.there

notation:40 "↑" => shift

def cons {Γ Δ : Context} {τ : Ty} (e : Δ ⊢ τ) (σ : Subst Γ Δ) : Subst (τ :: Γ) Δ
  | _, .here => e
  | _, .there a => σ a

infixr:60 " • " => cons

abbrev seq
  {Γ Δ Ψ : Context}
  (σ : Subst Γ Δ) (σ' : Subst Δ Ψ) :
  Subst Γ Ψ :=
  ⟪ σ' ⟫ ∘ σ

infixr:50 " ⨟ " => seq

end Subst

-- Relating original definitions to σ-algebra

namespace Rename

abbrev subst {Γ Δ : Context} (ρ : Rename Γ Δ) : Subst Γ Δ := Subst.ids ∘ ρ

@[simp]
theorem subst_ids
  {Γ : Context} :
  @Eq (Subst Γ Γ) (subst ids) Subst.ids := rfl
  
@[simp]
theorem subst_comp
  {Γ Δ Ψ : Context}
  (ρ : Rename Γ Δ) (ρ' : Rename Δ Ψ) :
  @Eq (Subst Γ Ψ) (subst (ρ' ∘ ρ)) (subst ρ ⨟ subst ρ') := rfl

@[simp]
theorem subst_ext
  {Γ Δ : Context} {τ : Ty}
  (ρ : Rename Γ Δ) :
  @Eq (Subst (τ :: Γ) (τ :: Δ)) (subst (ext ρ)) (Subst.exts (subst ρ)) :=
  let lemma {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → subst (ext ρ) a = Subst.exts (subst ρ) a
  | .here => rfl
  | .there a => rfl

  funext (fun _ => funext lemma)

@[simp]
theorem subst_shift
  {Γ : Context} {τ : Ty} :
  @Eq (Subst Γ (τ :: Γ)) (subst shift) Subst.shift := rfl

@[simp]
theorem subst_swap
  {Γ : Context} {τ τ' : Ty} :
  @Eq (Subst (τ' :: τ :: Γ) (τ :: τ' :: Γ)) (subst swap) ((Expr.var (Any.there Any.here)) • (Expr.var Any.here) • (Subst.shift ⨟ Subst.shift ⨟ Subst.ids)) :=
  let lemma {τ'' : Ty} : (a : (τ' :: τ :: Γ) ∋ τ'') → subst swap a = ((Expr.var (Any.there Any.here)) • (Expr.var Any.here) • (Subst.shift ⨟ Subst.shift ⨟ Subst.ids)) a
  | .here => rfl
  | .there .here => rfl
  | .there (.there a) => rfl

  funext (fun _ => funext lemma)

@[simp]
theorem rename_subst_subst
  {Γ Δ : Context} {τ : Ty}
  (ρ : Rename Γ Δ) :
  @Expr.rename _ _ τ ρ = Expr.subst (subst ρ) :=
  let rec lemma {Γ Δ : Context} (ρ : Rename Γ Δ) {τ : Ty} : (e : Γ ⊢ τ) → Expr.rename ρ e = (Expr.subst (subst ρ)) e
  | .var _ | .number _ | .string _ => rfl
  | .abstraction e => by simp only [Expr.rename, lemma ρ.ext e, subst_ext, Subst.exts, Expr.subst]
  | .application e₁ e₂ => by simp only [Expr.rename, Expr.subst, lemma ρ e₁, lemma ρ e₂]

  funext (lemma ρ)

end Rename

namespace Subst

@[simp]
theorem exts_cons_shift
  {Γ Δ : Context} {τ : Ty}
  (σ : Subst Γ Δ) :
  @Eq (Subst (τ :: Γ) (τ :: Δ)) (exts σ) (((Expr.var Any.here) • (σ ⨟ (↑)))) :=
  let lemma {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → exts σ a = ((Expr.var Any.here) • (σ ⨟ (↑))) a
  | .here => rfl
  | .there _ => by simp [exts, Expr.shift]; rfl

  funext (fun _ => funext lemma)

@[simp]
theorem subst_zero_cons_ids
  {Γ : Context} {τ : Ty}
  (e : Γ ⊢ τ) :
  @Eq (Subst (τ :: Γ) Γ) (zero e) (e • ids) :=
  let lemma {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → (zero e) a = (e • ids) a
  | .here => rfl
  | .there _ => rfl

  funext (fun _ => funext lemma)

end Subst

-- Rewrite system

namespace Subst

@[simp]
theorem subst_head
  {Γ : Context} {Δ : Context} {τ : Ty}
  (σ : Subst Γ Δ)
  (e : Δ ⊢ τ) :
  (⟪ e • σ ⟫) (Expr.var Any.here) = e := rfl

@[simp]
theorem subst_tail
  {Γ : Context} {Δ : Context} {τ : Ty}
  (σ : Subst Γ Δ)
  (e : Δ ⊢ τ) :
  @Eq (Subst Γ Δ) ((↑) ⨟ e • σ) σ := rfl

@[simp]
theorem subst_η
  {Γ : Context} {Δ : Context} {τ : Ty}
  (σ : Subst (τ :: Γ) Δ) :
  @Eq (Subst (τ :: Γ) Δ) ((⟪ σ ⟫) (Expr.var Any.here) • ((↑) ⨟ σ)) σ :=
  let lemma {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → ((⟪ σ ⟫) (Expr.var Any.here) • ((↑) ⨟ σ)) a = σ a
  | .here => rfl
  | .there _ => rfl

  funext (fun _ => funext lemma)

@[simp]
theorem zero_shift
  {Γ : Context} {τ : Ty} :
  @Eq (Subst (τ :: Γ) (τ :: Γ)) ((Expr.var Any.here) • (↑)) ids :=
  let lemma {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → ((Expr.var Any.here) • (↑)) a = ids a
  | .here => rfl
  | .there _ => rfl

  funext (fun _ => funext lemma)

@[simp]
theorem subst_id_left
  {Γ Δ : Context}
  (σ : Subst Γ Δ) :
  @Eq (Subst Γ Δ) (ids ⨟ σ) σ := rfl

@[simp]
theorem subst_id
  {Γ : Context} {τ : Ty} :
  @Eq ((Γ ⊢ τ) → Γ ⊢ τ) (⟪ ids⟫ ) id :=
  let rec lemma {Γ : Context} {τ : Ty} : (e : Γ ⊢ τ) → (⟪ ids ⟫) e = id e
  | .var _ => rfl
  | .number _ => rfl
  | .string _ => rfl
  | .abstraction e => by simp only [Expr.subst, lemma e, id_eq, exts_cons_shift, subst_id_left, zero_shift]
  | .application e₁ e₂ => by simp only [Expr.subst, lemma e₁, id_eq, lemma e₂]

  funext lemma

@[simp]
theorem subst_id_right
  {Γ Δ : Context}
  (σ : Subst Γ Δ) :
  @Eq (Subst Γ Δ) (σ ⨟ ids) σ :=
  let lemma {τ' : Ty} : (a : Γ ∋ τ') → (σ ⨟ ids) a = σ a := by simp only [Function.comp_apply, subst_id, id_eq, implies_true]

  funext (fun _ => funext lemma)

@[simp]
theorem subst_let
  {Γ Δ : Context} {τ τ' : Ty}
  (σ : Subst Γ Δ)
  (e : τ :: Γ ⊢ τ') :
  (⟪ σ ⟫) (Expr.abstraction e) = (Expr.abstraction ((⟪ (Expr.var Any.here) • (σ ⨟ (↑)) ⟫) e)) :=
by simp only [Expr.subst, exts_cons_shift]

@[simp]
theorem subst_application
  {Γ Δ : Context} {τ τ' : Ty} {σ : Subst Γ Δ} {e₁ : Γ ⊢ Ty.arrow τ τ'} {e₂ : Γ ⊢ τ} :
  (⟪ σ ⟫) (Expr.application e₁ e₂) = (Expr.application ((⟪ σ ⟫) e₁) ((⟪ σ ⟫) e₂)) := rfl

@[simp]
theorem subst_dist
  {Γ Δ Ψ : Context} {τ : Ty}
  (σ : Subst Γ Δ) (σ' : Subst Δ Ψ)
  (e : Δ ⊢ τ) :
  @Eq (Subst (τ :: Γ) Ψ) ((e • σ) ⨟ σ') ((⟪ σ' ⟫) e • (σ ⨟ σ')) :=
  let lemma {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → ((e • σ) ⨟ σ') a = ((⟪ σ' ⟫) e • (σ ⨟ σ')) a
  | .here => rfl
  | .there _ => rfl

  funext (fun _ => funext lemma)

theorem subst_shift_commuteᵣ
  {Γ Δ : Context} {τ τ' : Ty} {σ : Subst Γ Δ}
  (tys : List Ty) (e : tys ++ Γ ⊢ τ) :
  @Eq (tys ++ τ' :: Δ ⊢ τ) ((⟪ Subst.extsᵣ (Subst.exts σ) tys ⟫) (Expr.rename (Rename.extᵣ Rename.shift tys) e))
                           (Expr.rename (Rename.extᵣ Rename.shift tys) ((⟪ Subst.extsᵣ σ tys ⟫) e)) :=
  match τ, e with
  | τ, .var a => by
      let rec lemma
        {Γ Δ : Context} {τ τ' : Ty} {σ : Subst Γ Δ}
        (tys : List Ty) (a : tys ++ Γ ∋ τ):
        @Eq (tys ++ τ' :: Δ ⊢ τ) (extsᵣ (exts σ) tys (Rename.extᵣ Rename.shift tys a))
                                 (Expr.rename (Rename.extᵣ Rename.shift tys) (extsᵣ σ tys a)) := by
          match tys, a with
          | [], _ => rfl
          | ty :: tys, .here => rfl
          | ty :: tys, .there a =>
              simp only [Rename.extᵣ, Subst.extsᵣ, id]
              conv => lhs; dsimp only [Rename.ext]
              generalize h : (extsᵣ (exts σ) tys : {τ : Ty} → (tys ++ τ' :: Γ ∋ τ) → tys ++ τ' :: Δ ⊢ τ) = tmp
              dsimp only [Subst.exts]
              rw [← h]
              conv => rhs; dsimp only [Subst.exts]
              simp only [
                Expr.rename_comp_arg Rename.shift (Rename.ext (Rename.extᵣ Rename.shift tys)),
                Rename.shift_commute,
                ← Expr.rename_comp_arg (Rename.extᵣ Rename.shift tys) Rename.shift,
                ← @lemma Γ Δ τ τ' σ tys a
              ]

      dsimp only [Expr.rename, Expr.subst]
      exact lemma tys a
  | _, .number _ | _, .string _ => rfl
  | _, .abstraction e => by
      rename_i τ₁ τ₂
      dsimp only [Expr.rename, Expr.subst]
      have := @subst_shift_commuteᵣ _ _ τ₂ τ' σ (τ₁ :: tys) e
      congr
  | _, .application e₁ e₂ => by simp only [Expr.rename, Expr.subst, subst_shift_commuteᵣ tys e₁, subst_shift_commuteᵣ tys e₂]

theorem subst_shift_commute
  {Γ Δ : Context} {τ τ' : Ty} {σ : Subst Γ Δ}
  (e : Γ ⊢ τ) :
  @Eq (τ' :: Δ ⊢ τ) ((⟪ Subst.exts σ ⟫) (Expr.shift e)) (Expr.shift ((⟪ σ ⟫) e)) := by
  let h := @subst_shift_commuteᵣ Γ Δ τ τ' σ [] e
  simp only [Subst.extsᵣ, Rename.extᵣ, id] at h
  exact h

theorem exts_seq_dist
  {Γ Δ Ψ : Context} {τ : Ty}
  (σ : Subst Γ Δ) (σ' : Subst Δ Ψ) :
  @Eq (Subst (τ :: Γ) (τ :: Ψ)) (exts σ ⨟ exts σ') (exts (σ ⨟ σ')) :=
  let lemma {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → (exts σ ⨟ exts σ') a = exts (σ ⨟ σ') a
  | .here => rfl
  | .there a => by
      calc (exts σ ⨟ exts σ') (Any.there a)
        _ = (⟪ exts σ' ⟫) (Expr.shift (σ a)) := by rfl
        _ = Expr.shift ((⟪ σ' ⟫) (σ a)) := by exact subst_shift_commute (σ a)
        _ = _ := rfl

  funext (fun _ => funext lemma)

@[simp]
theorem subst_subst
  {Γ Δ Ψ : Context} {τ : Ty}
  (σ : Subst Γ Δ) (σ' : Subst Δ Ψ) :
  (e : Γ ⊢ τ) →
  (⟪ σ' ⟫) ((⟪ σ ⟫) e) = (⟪ σ ⨟ σ' ⟫) e
  | .var _ | .number _ | .string _ => rfl
  | .abstraction e => by simp only [Expr.subst, subst_subst (exts σ) (exts σ') e, exts_seq_dist σ σ']
  | .application e₁ e₂ => by simp only [Expr.subst, subst_subst σ σ' e₁, subst_subst σ σ' e₂]

@[simp]
theorem subst_assoc
  {Γ Δ Ψ ζ : Context}
  (σ : Subst Γ Δ) (σ' : Subst Δ Ψ) (σ'' : Subst Ψ ζ) :
  @Eq (Subst Γ ζ) ((σ ⨟ σ') ⨟ σ'') (σ ⨟ (σ' ⨟ σ'')) :=
  let lemma {τ : Ty} : (a : Γ ∋ τ) → ((σ ⨟ σ') ⨟ σ'') a = (σ ⨟ (σ' ⨟ σ'')) a := by simp

  funext (fun _ => funext lemma)

theorem subst_commute
  {Γ Δ : Context} {τ τ' : Ty}
  (σ : Subst Γ Δ) (e : (τ :: Γ) ⊢ τ') (e' : Γ ⊢ τ) :
  ((⟪ exts σ ⟫) e) [ (⟪ σ ⟫) e' ] = (⟪ σ ⟫) (e [ e' ]) := by simp

end Subst
