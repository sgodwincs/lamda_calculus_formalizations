import Stlc.Statics.Any
import Stlc.Statics.Context
import Stlc.Statics.Ty
import Stlc.Statics.Expr.Core
import Stlc.Statics.Expr.Rename

namespace Statics

abbrev Subst (Γ Δ : Context) : Type := ∀ {τ : Ty}, (Γ ∋ τ) → Δ ⊢ τ

abbrev ClosingSubst (Γ : Context) : Type := Subst Γ []

namespace Subst

def exts {Γ Δ : Context} {τ : Ty} (σ : Subst Γ Δ) : Subst (τ :: Γ) (τ :: Δ)
  | _, .here => Expr.var Any.here
  | _, .there a => Expr.rename Any.there (σ a)

def extsᵣ {Γ Δ : Context} (σ : Subst Γ Δ) : (τs : List Ty) → Subst (τs ++ Γ) (τs ++ Δ)
  | [], _ => σ
  | _ :: τs, _ => exts (extsᵣ σ τs)

def zero {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) : Subst (τ :: Γ) Γ
  | _, .here => e
  | _, .there a => Expr.var a

end Subst

namespace Expr

def subst {Γ Δ : Context} {τ : Ty} (σ : Subst Γ Δ) : (Γ ⊢ τ) → Δ ⊢ τ
  | .var a => σ a
  | .triv => Expr.triv
  | .pair e₁ e₂ => Expr.pair (e₁.subst σ) (e₂.subst σ)
  | .proj₁ e => Expr.proj₁ (e.subst σ)
  | .proj₂ e => Expr.proj₂ (e.subst σ)
  | .abstraction e => Expr.abstraction (e.subst σ.exts)
  | .application e₁ e₂ => Expr.application (e₁.subst σ) (e₂.subst σ)

notation:100 "⟪ " s " ⟫" => subst s

abbrev subst_zero {Γ : Context} {τ τ' : Ty} (e : Γ ⊢ τ) (e' : (τ :: Γ) ⊢ τ') : Γ ⊢ τ' := e'.subst (Subst.zero e)

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

abbrev seq {Γ Δ Ψ : Context} (σ : Subst Γ Δ) (σ' : Subst Δ Ψ) : Subst Γ Ψ := ⟪ σ' ⟫ ∘ σ

infixr:50 " ⨟ " => seq

end Subst

-- Relating original definitions to σ-algebra

namespace Rename

abbrev subst {Γ Δ : Context} (ρ : Rename Γ Δ) : Subst Γ Δ := Subst.ids ∘ ρ

@[simp]
theorem subst_ids {Γ : Context} : @Eq (Subst Γ Γ) (subst ids) Subst.ids := rfl
  
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
theorem subst_shift {Γ : Context} {τ : Ty} : @Eq (Subst Γ (τ :: Γ)) (subst shift) Subst.shift := rfl

@[simp]
theorem subst_swap
  {Γ : Context} {τ τ' : Ty} :
  @Eq (Subst (τ' :: τ :: Γ) (τ :: τ' :: Γ)) (subst swap) ((Expr.var (Any.there Any.here)) • (Expr.var Any.here) • ((↑) ⨟ (↑) ⨟ Subst.ids)) :=
  let lemma {τ'' : Ty} : (a : (τ' :: τ :: Γ) ∋ τ'') → subst swap a = ((Expr.var (Any.there Any.here)) • (Expr.var Any.here) • ((↑) ⨟ (↑) ⨟ Subst.ids)) a
  | .here => rfl
  | .there .here => rfl
  | .there (.there a) => rfl

  funext (fun _ => funext lemma)

@[simp]
theorem rename_subst_subst {Γ Δ : Context} {τ : Ty} (ρ : Rename Γ Δ) : @Expr.rename _ _ τ ρ = Expr.subst (subst ρ) :=
  let rec lemma {Γ Δ : Context} (ρ : Rename Γ Δ) {τ : Ty} : (e : Γ ⊢ τ) → Expr.rename ρ e = (Expr.subst (subst ρ)) e
  | .var _ | .triv => rfl
  | .pair e₁ e₂ => by simp only [Expr.rename, Expr.subst, lemma ρ e₁, lemma ρ e₂]
  | .proj₁ e | .proj₂ e => by simp only [Expr.rename, Expr.subst, lemma ρ e]
  | .abstraction e => by simp only [Expr.rename, Expr.subst, lemma ρ.ext e, subst_ext]
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
theorem subst_zero_cons_ids {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) : @Eq (Subst (τ :: Γ) Γ) (zero e) (e • ids) :=
  let lemma {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → (zero e) a = (e • ids) a
  | .here => rfl
  | .there _ => rfl

  funext (fun _ => funext lemma)

end Subst

-- Rewrite system

namespace Subst

@[simp]
theorem subst_head {Γ Δ : Context} {τ : Ty} (σ : Subst Γ Δ) (e : Δ ⊢ τ) : (⟪ e • σ ⟫) (Expr.var Any.here) = e := rfl

@[simp]
theorem subst_tail {Γ Δ : Context} {τ : Ty} (σ : Subst Γ Δ) (e : Δ ⊢ τ) : @Eq (Subst Γ Δ) ((↑) ⨟ e • σ) σ := rfl

@[simp]
theorem subst_η
  {Γ Δ : Context} {τ : Ty}
  (σ : Subst (τ :: Γ) Δ) :
  @Eq (Subst (τ :: Γ) Δ) ((⟪ σ ⟫) (Expr.var Any.here) • ((↑) ⨟ σ)) σ :=
  let lemma {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → ((⟪ σ ⟫) (Expr.var Any.here) • ((↑) ⨟ σ)) a = σ a
  | .here => rfl
  | .there _ => rfl

  funext (fun _ => funext lemma)

@[simp]
theorem zero_shift {Γ : Context} {τ : Ty} : @Eq (Subst (τ :: Γ) (τ :: Γ)) ((Expr.var Any.here) • (↑)) ids :=
  let lemma {τ' : Ty} : (a : (τ :: Γ) ∋ τ') → ((Expr.var Any.here) • (↑)) a = ids a
  | .here => rfl
  | .there _ => rfl

  funext (fun _ => funext lemma)

@[simp]
theorem subst_id_left {Γ Δ : Context} (σ : Subst Γ Δ) : @Eq (Subst Γ Δ) (ids ⨟ σ) σ := rfl

@[simp]
theorem subst_id {Γ : Context} {τ : Ty} : @Eq ((Γ ⊢ τ) → Γ ⊢ τ) (⟪ ids⟫ ) id :=
  let rec lemma {Γ : Context} {τ : Ty} : (e : Γ ⊢ τ) → (⟪ ids ⟫) e = id e
  | .var _ | .triv => rfl
  | .pair e₁ e₂ => by simp only [Expr.subst, lemma e₁, lemma e₂, id_eq]
  | .proj₁ e | .proj₂ e => by simp only [Expr.subst, lemma e, id_eq]
  | .abstraction e => by simp only [Expr.subst, lemma e, id_eq, exts_cons_shift, subst_id_left, zero_shift]
  | .application e₁ e₂ => by simp only [Expr.subst, lemma e₁, id_eq, lemma e₂]

  funext lemma

@[simp]
theorem subst_id_right {Γ Δ : Context} (σ : Subst Γ Δ) : @Eq (Subst Γ Δ) (σ ⨟ ids) σ :=
  let lemma {τ' : Ty} : (a : Γ ∋ τ') → (σ ⨟ ids) a = σ a := by simp only [Function.comp_apply, subst_id, id_eq, implies_true]

  funext (fun _ => funext lemma)

@[simp]
theorem subst_pair
  {Γ Δ : Context} {τ : Ty}
  (σ : Subst Γ Δ)
  (e₁ : Γ ⊢ τ)
  (e₂ : Γ ⊢ τ) :
  (⟪ σ ⟫) (Expr.pair e₁ e₂) = (Expr.pair ((⟪ σ ⟫) e₁) ((⟪ σ ⟫) e₂)) := rfl

@[simp]
theorem subst_proj₁
  {Γ Δ : Context} {τ₁ τ₂ : Ty}
  (σ : Subst Γ Δ)
  (e : Γ ⊢ Ty.prod τ₁ τ₂) :
  (⟪ σ ⟫) (Expr.proj₁ e) = (Expr.proj₁ ((⟪ σ ⟫) e)) := rfl

@[simp]
theorem subst_proj₂
  {Γ Δ : Context} {τ₁ τ₂ : Ty}
  (σ : Subst Γ Δ)
  (e : Γ ⊢ Ty.prod τ₁ τ₂) :
  (⟪ σ ⟫) (Expr.proj₂ e) = (Expr.proj₂ ((⟪ σ ⟫) e)) := rfl

@[simp]
theorem subst_abstraction
  {Γ Δ : Context} {τ τ' : Ty}
  (σ : Subst Γ Δ)
  (e : τ :: Γ ⊢ τ') :
  (⟪ σ ⟫) (Expr.abstraction e) = (Expr.abstraction ((⟪ σ.exts ⟫) e)) :=
by
  simp only [Expr.subst, exts_cons_shift]

@[simp]
theorem subst_application
  {Γ Δ : Context} {τ τ' : Ty}
  (σ : Subst Γ Δ)
  (e₁ : Γ ⊢ Ty.arrow τ τ') (e₂ : Γ ⊢ τ) :
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
  (τs : List Ty) (e : τs ++ Γ ⊢ τ) :
  @Eq (τs ++ τ' :: Δ ⊢ τ) ((⟪ Subst.extsᵣ (Subst.exts σ) τs ⟫) (Expr.rename (Rename.extᵣ Rename.shift τs) e))
                           (Expr.rename (Rename.extᵣ Rename.shift τs) ((⟪ Subst.extsᵣ σ τs ⟫) e)) :=
  match τ, e with
  | τ, .var a => by
      let rec lemma
        {Γ Δ : Context} {τ τ' : Ty} {σ : Subst Γ Δ}
        (τs : List Ty) (a : τs ++ Γ ∋ τ):
        @Eq (τs ++ τ' :: Δ ⊢ τ) (extsᵣ (exts σ) τs (Rename.extᵣ Rename.shift τs a))
                                 (Expr.rename (Rename.extᵣ Rename.shift τs) (extsᵣ σ τs a)) := by
          match τs, a with
          | [], _ => rfl
          | _ :: _, .here => rfl
          | _ :: τs, .there a =>
              simp only [Rename.extᵣ, Subst.extsᵣ, id]
              conv => lhs; dsimp only [Rename.ext]
              generalize h : (extsᵣ (exts σ) τs : {τ : Ty} → (τs ++ τ' :: Γ ∋ τ) → τs ++ τ' :: Δ ⊢ τ) = tmp
              dsimp only [Subst.exts]
              rw [← h]
              conv => rhs; dsimp only [Subst.exts]
              simp only [
                Expr.rename_comp_arg Rename.shift (Rename.ext (Rename.extᵣ Rename.shift τs)),
                Rename.shift_commute,
                ← Expr.rename_comp_arg (Rename.extᵣ Rename.shift τs) Rename.shift,
                ← @lemma Γ Δ τ τ' σ τs a
              ]

      dsimp only [Expr.rename, Expr.subst]
      exact lemma τs a
  | _, .triv => rfl
  | _, .pair e₁ e₂ => by
      rename_i τ₁ τ₂
      simp only [Expr.rename, Expr.subst, subst_shift_commuteᵣ τs e₁, subst_shift_commuteᵣ τs e₂]
  | _, .proj₁ e | _, .proj₂ e => by simp only [Expr.rename, Expr.subst, subst_shift_commuteᵣ τs e]
  | _, .abstraction e => by
      rename_i τ₁ τ₂
      dsimp only [Expr.rename, Expr.subst]
      have := @subst_shift_commuteᵣ _ _ τ₂ τ' σ (τ₁ :: τs) e
      congr
  | _, .application e₁ e₂ => by simp only [Expr.rename, Expr.subst, subst_shift_commuteᵣ τs e₁, subst_shift_commuteᵣ τs e₂]

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

theorem extsᵣ_seq_dist
  {Γ Δ Ψ : Context}
  (σ : Subst Γ Δ) (σ' : Subst Δ Ψ) :
  (τs : List Ty) →
  @Eq (Subst (τs ++ Γ) (τs ++ Ψ)) (extsᵣ σ τs ⨟ extsᵣ σ' τs) (extsᵣ (σ ⨟ σ') τs)
  | [] => rfl
  | τ :: τs => by
      simp only [extsᵣ, id_eq]
      rw [exts_seq_dist, extsᵣ_seq_dist σ σ' τs]

@[simp]
theorem subst_subst
  {Γ Δ Ψ : Context} {τ : Ty}
  (σ : Subst Γ Δ) (σ' : Subst Δ Ψ) :
  (e : Γ ⊢ τ) →
  (⟪ σ' ⟫) ((⟪ σ ⟫) e) = (⟪ σ ⨟ σ' ⟫) e
  | .var _ | .triv => rfl
  | .pair e₁ e₂ => by simp only [Expr.subst, subst_subst σ σ' e₁, subst_subst σ σ' e₂]
  | .proj₁ e | .proj₂ e => by simp only [Expr.subst, subst_subst σ σ' e]
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
