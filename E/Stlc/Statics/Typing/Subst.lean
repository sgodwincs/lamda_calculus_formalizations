import Stlc.Statics.Any
import Stlc.Statics.Context
import Stlc.Statics.Ty
import Stlc.Statics.Typing.Core
import Stlc.Statics.Typing.Rename

namespace Statics

abbrev Subst (Γ Δ : Context) : Type :=
  ∀ {τ : Ty}, (Γ ∋ τ) → Δ ⊢ τ

abbrev ClosingSubst (Γ : Context) : Type := Subst Γ []

namespace Subst

def exts
  {Γ Δ : Context} {τ : Ty}
  (σ : Subst Γ Δ) :
  Subst (τ :: Γ) (τ :: Δ)
  | _, .here => Typing.var Any.here
  | _, .there a => Typing.rename Any.there (σ a)

def extsᵣ
  {Γ Δ : Context}
  (σ : Subst Γ Δ) :
  (tys : List Ty) → Subst (tys ++ Γ) (tys ++ Δ)
  | .nil, _ => by simp only [List.nil_append]; exact σ
  | τ :: tys, _ => by
      simp only [List.cons_append]
      exact exts (extsᵣ σ tys)

def zero {Γ : Context} {τ : Ty} (t : Γ ⊢ τ) : Subst (τ :: Γ) Γ
  | _, .here => t
  | _, .there a => Typing.var a

end Subst

namespace Typing

def subst
  {Γ Δ : Context} {τ : Ty}
  (σ : Subst Γ Δ) :
  (Γ ⊢ τ) →
  Δ ⊢ τ
  | .var a => σ a
  | .number num => Typing.number num
  | .string s => Typing.string s
  | .plus t₁ t₂ => Typing.plus (subst σ t₁) (subst σ t₂)
  | .times t₁ t₂ => Typing.times (subst σ t₁) (subst σ t₂)
  | .concatenate t₁ t₂ => Typing.concatenate (subst σ t₁) (subst σ t₂)
  | .length t => Typing.length (t.subst σ)
  | .let t₁ t₂ => Typing.let (subst σ t₁) (t₂.subst (Subst.exts σ))

notation:100 "⟪ " s " ⟫" => subst s

abbrev subst_zero
  {Γ : Context} {τ τ' : Ty}
  (t : Γ ⊢ τ)
  (t' : (τ :: Γ) ⊢ τ') :
  Γ ⊢ τ' := subst (Subst.zero t) t'

notation:100 t " [ " t' " ]" => subst_zero t' t

end Typing

namespace Subst

abbrev ids {Γ : Context} : Subst Γ Γ := Typing.var

abbrev shift {Γ : Context} {τ : Ty} : Subst Γ (τ :: Γ) := Typing.var ∘ Any.there

notation:40 "↑" => shift

def cons {Γ Δ : Context} {τ : Ty} (t : Δ ⊢ τ) (σ : Subst Γ Δ) : Subst (τ :: Γ) Δ
  | _, .here => t
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

abbrev subst  {Γ Δ : Context} (ρ : Rename Γ Δ) : Subst Γ Δ := Subst.ids ∘ ρ

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
  {Γ : Context} {τ₁ τ₂ : Ty} :
  @Eq (Subst (τ₂ :: τ₁ :: Γ) (τ₁ :: τ₂ :: Γ)) (subst swap) ((Typing.var (Any.there Any.here)) • (Typing.var Any.here) • (Subst.shift ⨟ Subst.shift ⨟ Subst.ids)) :=
  let lemma {τ : Ty} : (a : (τ₂ :: τ₁ :: Γ) ∋ τ) → subst swap a = ((Typing.var (Any.there Any.here)) • (Typing.var Any.here) • (Subst.shift ⨟ Subst.shift ⨟ Subst.ids)) a
  | .here => rfl
  | .there .here => rfl
  | .there (.there a) => rfl

  funext (fun _ => funext lemma)

@[simp]
theorem rename_subst_subst
  {Γ Δ : Context} {τ : Ty}
  (ρ : Rename Γ Δ) :
  @Typing.rename _ _ τ ρ = Typing.subst (subst ρ) :=
  let rec lemma {Γ Δ : Context} (ρ : Rename Γ Δ) {τ : Ty} : (t : Γ ⊢ τ) → Typing.rename ρ t = (Typing.subst (subst ρ)) t
  | .var _ | .number _ | .string _ => rfl
  | .plus e₁ e₂ => by simp only [Typing.rename, lemma ρ e₁, lemma ρ e₂, Typing.subst]
  | .times e₁ e₂ => by simp only [Typing.rename, lemma ρ e₁, lemma ρ e₂, Typing.subst]
  | .concatenate e₁ e₂ => by simp only [Typing.rename, lemma ρ e₁, lemma ρ e₂, Typing.subst]
  | .length e => by simp only [Typing.rename, lemma ρ e, Typing.subst]
  | .let e₁ e₂ => by simp only [Typing.rename, lemma ρ e₁, lemma ρ.ext e₂, subst_ext, Subst.exts, Typing.subst]

  funext (lemma ρ)

end Rename

namespace Subst

@[simp]
theorem exts_cons_shift
  {Γ Δ : Context} {τ : Ty}
  (σ : Subst Γ Δ) :
  @Eq (Subst (τ :: Γ) (τ :: Δ)) (exts σ) (((Typing.var Any.here) • (σ ⨟ (↑)))) :=
  let lemma {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → exts σ a = ((Typing.var Any.here) • (σ ⨟ (↑))) a
  | .here => rfl
  | .there _ => by simp [exts, Typing.shift]; rfl

  funext (fun _ => funext lemma)

@[simp]
theorem subst_zero_cons_ids
  {Γ : Context} {τ : Ty}
  (t : Γ ⊢ τ) :
  @Eq (Subst (τ :: Γ) Γ) (zero t) (t • ids) :=
  let lemma {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → (zero t) a = (t • ids) a
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
  (t : Δ ⊢ τ) :
  (⟪ t • σ ⟫) (Typing.var Any.here) = t := rfl

@[simp]
theorem subst_tail
  {Γ : Context} {Δ : Context} {τ : Ty}
  (σ : Subst Γ Δ)
  (t : Δ ⊢ τ) :
  @Eq (Subst Γ Δ) ((↑) ⨟ t • σ) σ := rfl

@[simp]
theorem subst_η
  {Γ : Context} {Δ : Context} {τ : Ty}
  (σ : Subst (τ :: Γ) Δ) :
  @Eq (Subst (τ :: Γ) Δ) ((⟪ σ ⟫) (Typing.var Any.here) • ((↑) ⨟ σ)) σ :=
  let lemma {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → ((⟪ σ ⟫) (Typing.var Any.here) • ((↑) ⨟ σ)) a = σ a
  | .here => rfl
  | .there _ => rfl

  funext (fun _ => funext lemma)

@[simp]
theorem zero_shift
  {Γ : Context} {τ : Ty} :
  @Eq (Subst (τ :: Γ) (τ :: Γ)) ((Typing.var Any.here) • (↑)) ids :=
  let lemma {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → ((Typing.var Any.here) • (↑)) a = ids a
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
  let rec lemma {Γ : Context} {τ : Ty} : (t : Γ ⊢ τ) → (⟪ ids ⟫) t = id t
  | .var _ => rfl
  | .number _ => rfl
  | .string _ => rfl
  | .plus e₁ e₂ => by simp only [Typing.subst, lemma e₁, id_eq, lemma e₂]
  | .times e₁ e₂ => by simp only [Typing.subst, lemma e₁, id_eq, lemma e₂]
  | .concatenate e₁ e₂ => by simp only [Typing.subst, lemma e₁, id_eq, lemma e₂]
  | .length e => by simp only [Typing.subst, lemma e, id_eq]
  | .let e₁ e₂ => by simp only [Typing.subst, lemma e₁, id_eq, exts_cons_shift, subst_id_left, zero_shift, lemma e₂]

  funext lemma

@[simp]
theorem subst_id_right
  {Γ Δ : Context}
  (σ : Subst Γ Δ) :
  @Eq (Subst Γ Δ) (σ ⨟ ids) σ :=
  let lemma {τ' : Ty} : (a : Γ ∋ τ') → (σ ⨟ ids) a = σ a := by simp only [Function.comp_apply, subst_id, id_eq, implies_true]

  funext (fun _ => funext lemma)

@[simp]
theorem subst_plus
  {Γ Δ : Context} {σ : Subst Γ Δ} {t₁ t₂ : Γ ⊢ Ty.number} :
  (⟪ σ ⟫) (Typing.plus t₁ t₂) = (Typing.plus ((⟪ σ ⟫) t₁) ((⟪ σ ⟫) t₂)) := rfl

@[simp]
theorem subst_times
  {Γ Δ : Context} {σ : Subst Γ Δ} {t₁ t₂ : Γ ⊢ Ty.number} :
  (⟪ σ ⟫) (Typing.times t₁ t₂) = (Typing.times ((⟪ σ ⟫) t₁) ((⟪ σ ⟫) t₂)) := rfl

@[simp]
theorem subst_concatenate
  {Γ Δ : Context} {σ : Subst Γ Δ} {t₁ t₂ : Γ ⊢ Ty.string} :
  (⟪ σ ⟫) (Typing.concatenate t₁ t₂) = (Typing.concatenate ((⟪ σ ⟫) t₁) ((⟪ σ ⟫) t₂)) := rfl

@[simp]
theorem subst_length
  {Γ Δ : Context} {σ : Subst Γ Δ} {t : Γ ⊢ Ty.string} :
  (⟪ σ ⟫) (Typing.length t) = (Typing.length ((⟪ σ ⟫) t)) := rfl

@[simp]
theorem subst_let
  {Γ Δ : Context} {τ₁ τ₂ : Ty}
  (σ : Subst Γ Δ)
  (t₁ : Γ ⊢ τ₁) (t₂ : (τ₁ :: Γ) ⊢ τ₂) :
  (⟪ σ ⟫) (Typing.let t₁ t₂) = (Typing.let ((⟪ σ ⟫) t₁) ((⟪ (Typing.var Any.here) • (σ ⨟ (↑)) ⟫) t₂)) :=
by simp only [Typing.subst, exts_cons_shift]

@[simp]
theorem subst_dist
  {Γ Δ Ψ : Context} {τ : Ty}
  (σ : Subst Γ Δ) (σ' : Subst Δ Ψ)
  (t : Δ ⊢ τ) :
  @Eq (Subst (τ :: Γ) Ψ) ((t • σ) ⨟ σ') ((⟪ σ' ⟫) t • (σ ⨟ σ')) :=
  let lemma {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → ((t • σ) ⨟ σ') a = ((⟪ σ' ⟫) t • (σ ⨟ σ')) a
  | .here => rfl
  | .there _ => rfl

  funext (fun _ => funext lemma)

theorem subst_shift_commuteᵣ
  {Γ Δ : Context} {τ τ' : Ty} {σ : Subst Γ Δ}
  (tys : List Ty) (t : tys ++ Γ ⊢ τ) :
  @Eq (tys ++ τ' :: Δ ⊢ τ) ((⟪ Subst.extsᵣ (Subst.exts σ) tys ⟫) (Typing.rename (Rename.extᵣ Rename.shift tys) t))
                           (Typing.rename (Rename.extᵣ Rename.shift tys) ((⟪ Subst.extsᵣ σ tys ⟫) t)) :=
  match τ, t with
  | τ, .var a => by
      let rec lemma
        {Γ Δ : Context} {τ τ' : Ty} {σ : Subst Γ Δ}
        (tys : List Ty) (a : tys ++ Γ ∋ τ):
        @Eq (tys ++ τ' :: Δ ⊢ τ) (extsᵣ (exts σ) tys (Rename.extᵣ Rename.shift tys a))
                                 (Typing.rename (Rename.extᵣ Rename.shift tys) (extsᵣ σ tys a)) := by
          match tys, a with
          | [], _ => rfl
          | ty :: tys, .here => rfl
          | ty :: tys, .there a =>
              simp only [Rename.extᵣ, Subst.extsᵣ, id]
              conv => lhs; simp only [Rename.ext]
              generalize h : (extsᵣ (exts σ) tys : {τ : Ty} → (tys ++ τ' :: Γ ∋ τ) → tys ++ τ' :: Δ ⊢ τ) = tmp
              simp only [Subst.exts]
              rw [← h]
              conv => rhs; simp only [Subst.exts]
              simp only [
                Typing.rename_comp_arg Rename.shift (Rename.ext (Rename.extᵣ Rename.shift tys)),
                Rename.shift_commute,
                ← Typing.rename_comp_arg (Rename.extᵣ Rename.shift tys) Rename.shift,
                ← @lemma Γ Δ τ τ' σ tys a
              ]

      simp only [Typing.rename, Typing.subst]
      exact lemma tys a
  | _, .number _ | _, .string _ => rfl
  | _, .plus t₁ t₂ => by simp only [Typing.rename, Typing.subst, subst_shift_commuteᵣ tys t₁, subst_shift_commuteᵣ tys t₂]
  | _, .times t₁ t₂ => by simp only [Typing.rename, Typing.subst, subst_shift_commuteᵣ tys t₁, subst_shift_commuteᵣ tys t₂]
  | _, .concatenate t₁ t₂ => by simp only [Typing.rename, Typing.subst, subst_shift_commuteᵣ tys t₁, subst_shift_commuteᵣ tys t₂]
  | _, .length t => by simp only [Typing.rename, Typing.subst, subst_shift_commuteᵣ tys t]
  | _, .let t₁ t₂ => by
      rename_i τ₂ τ₁
      simp only [Typing.rename, Typing.subst, subst_shift_commuteᵣ tys t₁]
      congr
      
      let h₂ := @subst_shift_commuteᵣ _ _ τ₂ τ' σ (τ₁ :: tys) t₂
      simp only [Subst.extsᵣ, Rename.extᵣ, id] at h₂
      exact h₂

-- This proof gave me a significant amount of trouble. I originally tried to prove it directly by induction on t but
-- I got stuck on the `let` case. I had to use `swap` on the inductive hypothesis for `t₂` but this then required me to
-- try proving a similar commute theorem about `swap`. In the process of that theorem, I needed this theorem to prove it
-- but even that wasn't enough assuming I could prove termination. I came across a scenario where the `exts` and `ext`
-- repeated themselves and I needed a more general form of this theorem. After some long thought, I was able to define
-- the stronger theorem `subst_shift_commmuteᵣ` above. The `let` case actually become trivial to prove, but the variable
-- case became a bit harder. Just sharing some thoughts on how I arrived at this proof :)
theorem subst_shift_commute
  {Γ Δ : Context} {τ τ' : Ty} {σ : Subst Γ Δ}
  (t : Γ ⊢ τ) :
  @Eq (τ' :: Δ ⊢ τ) ((⟪ Subst.exts σ ⟫) (Typing.shift t)) (Typing.shift ((⟪ σ ⟫) t)) := by
  let h := @subst_shift_commuteᵣ Γ Δ τ τ' σ [] t
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
        _ = (⟪ exts σ' ⟫) (Typing.shift (σ a)) := by rfl
        _ = Typing.shift ((⟪ σ' ⟫) (σ a)) := by exact subst_shift_commute (σ a)
        _ = _ := rfl

  funext (fun _ => funext lemma)

@[simp]
theorem subst_subst
  {Γ Δ Ψ : Context} {τ : Ty}
  (σ : Subst Γ Δ) (σ' : Subst Δ Ψ) (t : Γ ⊢ τ) :
  (⟪ σ' ⟫) ((⟪ σ ⟫) t) = (⟪ σ ⨟ σ' ⟫) t :=
  match t with
  | .var _ | .number _ | .string _ => rfl
  | .plus e₁ e₂ => by simp only [Typing.subst, subst_subst σ σ' e₁, subst_subst σ σ' e₂]
  | .times e₁ e₂ => by simp only [Typing.subst, subst_subst σ σ' e₁, subst_subst σ σ' e₂]
  | .concatenate e₁ e₂ => by simp only [Typing.subst, subst_subst σ σ' e₁, subst_subst σ σ' e₂]
  | .length e => by simp only [Typing.subst, subst_subst σ σ' e]
  | .let e₁ e₂ => by simp only [Typing.subst, subst_subst σ σ' e₁, subst_subst (exts σ) (exts σ') e₂, exts_seq_dist σ σ']

@[simp]
theorem subst_assoc
  {Γ Δ Ψ ζ : Context}
  (σ : Subst Γ Δ) (σ' : Subst Δ Ψ) (σ'' : Subst Ψ ζ) :
  @Eq (Subst Γ ζ) ((σ ⨟ σ') ⨟ σ'') (σ ⨟ (σ' ⨟ σ'')) :=
  let lemma {τ : Ty} : (a : Γ ∋ τ) → ((σ ⨟ σ') ⨟ σ'') a = (σ ⨟ (σ' ⨟ σ'')) a := by simp

  funext (fun _ => funext lemma)

theorem subst_commute
  {Γ Δ : Context} {τ τ' : Ty}
  (σ : Subst Γ Δ) (t : (τ :: Γ) ⊢ τ') (t' : Γ ⊢ τ) :
  ((⟪ exts σ ⟫) t) [ (⟪ σ ⟫) t' ] = (⟪ σ ⟫) (t [ t' ]) := by simp

end Subst
