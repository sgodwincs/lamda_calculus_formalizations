import Aesop

import E.Dynamics.Normal
import E.Dynamics.Progress
import E.Dynamics.Transition
import E.Statics

open Statics

namespace Dynamics

structure NormalizesTo {Γ : Context} {τ : Ty} (t t' : Γ ⊢ τ) where
  mtr : t ⟶* t'
  norm : Normal t'

structure WeaklyNormalizing {Γ : Context} {τ : Ty} (t : Γ ⊢ τ) where
  {t' : Γ ⊢ τ}
  normalizes : NormalizesTo t t'

notation:20 t " ⇓ " t' => NormalizesTo t t'
notation:20 t " ⇓" => WeaklyNormalizing t

structure Stuck {Γ : Context} {τ : Ty} (t : Γ ⊢ τ) where
  norm : Normal t
  not_val : Value t → Empty

namespace Neutral

def stuck {Γ : Context} {τ : Ty} {t : Γ ⊢ τ} (neut : Neutral t) : Stuck t := ⟨neut.normal, neut.not_a_value⟩

end Neutral

def _root_.Statics.Typing.not_stuck {τ : Ty} (t : ⊢ τ) (stuck : Stuck t) : Empty :=
  let ⟨norm, not_val⟩ := stuck
  match t.progress with
  | .step tr => Empty.elim (Normal.does_not_reduce norm tr)
  | .done val => Empty.elim (not_val val)

namespace WeaklyNormalizing

def preserves_forward_step
  {Γ : Context} {τ : Ty} {t t' : Γ ⊢ τ} :
  (t ⇓) →
  (t ⟶ t') →
  (t' ⇓)
  | ⟨.trans .(_) tr' tr'',  norm''⟩, tr => by
      simp only [Transition.deterministic tr tr']
      exact ⟨tr'', norm''⟩
  | ⟨.refl _, norm''⟩, tr => Empty.elim (norm''.does_not_reduce tr)

def preserves_backward_step
  {Γ : Context} {τ : Ty} {t t' : Γ ⊢ τ} :
  (t' ⇓) →
  (t ⟶ t') →
  (t ⇓)
  | ⟨mtr, norm''⟩, tr => ⟨Transitionᵣₜ.trans t tr mtr, norm''⟩

end WeaklyNormalizing

-- Proof of weak normalization based on http://www.cs.cmu.edu/~rwh/courses/chtt/pdfs/kripke-steps.pdf
-- It's a bit simpler here since there are only base types.
private def HereditarilyNormalizing {Γ : Context} {τ : Ty} (t : Γ ⊢ τ) : Type := t ⇓

private abbrev HereditarilyNormalizingSubst
  {Γ Δ : Context} (σ : Subst Γ Δ) :=
  ∀ {τ : Ty}, (a : Γ ∋ τ) → HereditarilyNormalizing (σ a)

private def hereditarily_normalizing
  {Γ Δ : Context} {τ : Ty} {σ : Subst Γ Δ} :
  (t : Γ ⊢ τ) →
  (hn_σ : HereditarilyNormalizingSubst σ) →
  HereditarilyNormalizing ((⟪ σ ⟫) t)
  | .var a, hn_σ => hn_σ a
  | .number num, _ => ⟨Transitionᵣₜ.refl _, Value.number.normal⟩
  | .string s, _ => ⟨Transitionᵣₜ.refl _, Value.string.normal⟩
  | .plus t₁ t₂, hn_σ =>
      let ⟨mtr₁, norm₁⟩ := hereditarily_normalizing t₁ hn_σ
      let ⟨mtr₂, norm₂⟩ := hereditarily_normalizing t₂ hn_σ

      match norm₁ with
      | .value .number =>
          match norm₂ with
          | .value .number =>
              ⟨
                calc
                  _ ⟶* _ := Transitionᵣₜ.ξ_plus₁ mtr₁
                  _ ⟶* _ := Transitionᵣₜ.ξ_plus₂ Value.number.normal mtr₂
                  _ ⟶ _ := Transition.β_plus Value.number.normal Value.number.normal,
                Value.number.normal
              ⟩
          | .neutral neut₂ =>
              ⟨
                calc
                  _ ⟶* _ := Transitionᵣₜ.ξ_plus₁ mtr₁
                  _ ⟶* _ := Transitionᵣₜ.ξ_plus₂ Value.number.normal mtr₂,
                (Neutral.plus₂ Value.number neut₂).normal
              ⟩
      | .neutral neut₁ =>
          ⟨
            calc
              _ ⟶* _ := Transitionᵣₜ.ξ_plus₁ mtr₁
              _ ⟶* _ := Transitionᵣₜ.ξ_plus₂ neut₁.normal mtr₂,
            (Neutral.plus₁ neut₁ norm₂).normal
          ⟩
  | .times t₁ t₂, hn_σ =>
      let ⟨mtr₁, norm₁⟩ := hereditarily_normalizing t₁ hn_σ
      let ⟨mtr₂, norm₂⟩ := hereditarily_normalizing t₂ hn_σ

      match norm₁ with
      | .value .number =>
          match norm₂ with
          | .value .number =>
              ⟨
                calc
                  _ ⟶* _ := Transitionᵣₜ.ξ_times₁ mtr₁
                  _ ⟶* _ := Transitionᵣₜ.ξ_times₂ Value.number.normal mtr₂
                  _ ⟶ _ := Transition.β_times Value.number.normal Value.number.normal,
                Value.number.normal
              ⟩
          | .neutral neut₂ =>
              ⟨
                calc
                  _ ⟶* _ := Transitionᵣₜ.ξ_times₁ mtr₁
                  _ ⟶* _ := Transitionᵣₜ.ξ_times₂ Value.number.normal mtr₂,
                (Neutral.times₂ Value.number neut₂).normal
              ⟩
      | .neutral neut₁ =>
          ⟨
            calc
              _ ⟶* _ := Transitionᵣₜ.ξ_times₁ mtr₁
              _ ⟶* _ := Transitionᵣₜ.ξ_times₂ neut₁.normal mtr₂,
            (Neutral.times₁ neut₁ norm₂).normal
          ⟩
  | .concatenate t₁ t₂, hn_σ =>
      let ⟨mtr₁, norm₁⟩ := hereditarily_normalizing t₁ hn_σ
      let ⟨mtr₂, norm₂⟩ := hereditarily_normalizing t₂ hn_σ

      match norm₁ with
      | .value .string =>
          match norm₂ with
          | .value .string =>
              ⟨
                calc
                  _ ⟶* _ := Transitionᵣₜ.ξ_concatenate₁ mtr₁
                  _ ⟶* _ := Transitionᵣₜ.ξ_concatenate₂ Value.string.normal mtr₂
                  _ ⟶ _ := Transition.β_concatenate Value.string.normal Value.string.normal,
                Value.string.normal
              ⟩
          | .neutral neut₂ =>
              ⟨
                calc
                  _ ⟶* _ := Transitionᵣₜ.ξ_concatenate₁ mtr₁
                  _ ⟶* _ := Transitionᵣₜ.ξ_concatenate₂ Value.string.normal mtr₂,
                (Neutral.concatenate₂ Value.string neut₂).normal
              ⟩
      | .neutral neut₁ =>
          ⟨
            calc
              _ ⟶* _ := Transitionᵣₜ.ξ_concatenate₁ mtr₁
              _ ⟶* _ := Transitionᵣₜ.ξ_concatenate₂ neut₁.normal mtr₂,
            (Neutral.concatenate₁ neut₁ norm₂).normal
          ⟩
  | .length t, hn_σ =>
      let ⟨mtr, norm⟩ := hereditarily_normalizing t hn_σ
      match norm with
      | .value .string =>
          ⟨
            calc
              _ ⟶* _ := Transitionᵣₜ.ξ_length mtr
              _ ⟶ _ := Transition.β_length Value.string.normal,
            Value.number.normal
          ⟩
      | .neutral neut => ⟨Transitionᵣₜ.ξ_length mtr, (Neutral.length neut).normal⟩
  | @Typing.let _ τ₁ τ₂ t₁ t₂, hn_σ => by
      let ⟨mtr₁, norm₁⟩ := hereditarily_normalizing t₁ hn_σ
      rename_i t₁'

      let σ' : Subst (τ₁ :: Γ) Δ
      | _, .here => t₁'
      | _, .there a => σ a

      let hn_σ' : HereditarilyNormalizingSubst σ'
      | _, .here => ⟨Transitionᵣₜ.refl _, norm₁⟩
      | _, .there a => hn_σ a

      let ⟨mtr₂, norm₂⟩ := hereditarily_normalizing t₂ hn_σ'
      
      exact ⟨
        calc (⟪ σ ⟫) (Typing.let t₁ t₂)
          _ ⟶* _ := by exact Transitionᵣₜ.ξ_let mtr₁
          _ ⟶ _ := by exact Transition.β_let rfl norm₁
          _ ⟶* _ := by
            simp only [
                Subst.exts_cons_shift, Subst.subst_subst, Subst.subst_zero_cons_ids, Subst.subst_dist,
                Subst.subst_assoc, Subst.subst_tail, Subst.subst_id_right
            ]
            exact mtr₂,
        norm₂
      ⟩

private def hereditarily_normalizing_weakly_normalizing
  {Γ : Context} {τ : Ty} {t : Γ ⊢ τ}
  (hn : HereditarilyNormalizing t) :
  WeaklyNormalizing t := hn

private def ids_hereditarily_normalizing_subst
  {Γ : Context} : HereditarilyNormalizingSubst (@Subst.ids Γ)
  | _, a => by
      unfold HereditarilyNormalizing
      unfold Subst.ids
      exact ⟨Transitionᵣₜ.refl _, (Neutral.var a).normal⟩

def _root_.Statics.Typing.weakly_normalizing
  {Γ : Context} {τ : Ty}
  (t : Γ ⊢ τ) :
  WeaklyNormalizing t := by
  let wn := hereditarily_normalizing t ids_hereditarily_normalizing_subst
  simp at wn
  exact hereditarily_normalizing_weakly_normalizing wn

def _root_.Statics.Typing.normal
  {Γ : Context} {τ : Ty}
  (t : Γ ⊢ τ) :
  Γ ⊢ τ := t.weakly_normalizing.t'

@[simp]
theorem _root_.Statics.Typing.normal_idempotent
  {Γ : Context} {τ : Ty}
  (t : Γ ⊢ τ) :
  t.normal.normal = t.normal := by
  unfold Typing.normal
  
  let { t', normalizes := ⟨_, norm⟩ } := t.weakly_normalizing
  let ⟨mtr', _⟩ := t'.weakly_normalizing
  simp only

  match mtr' with
  | .refl _ => rfl
  | .trans _ tr _ => exact Empty.elim (Normal.does_not_reduce norm tr)

def _root_.Statics.Typing.step_count
  {Γ : Context} {τ : Ty}
  (t : Γ ⊢ τ) : Nat := t.weakly_normalizing.normalizes.mtr.length

theorem Transition.step_count_decreases
  {Γ : Context} {τ : Ty} {t₁ t₂ : Γ ⊢ τ} (tr₁ : t₁ ⟶ t₂) :
  t₂.step_count < t₁.step_count := by
  let rec irrelevant'
    {Γ : Context} {τ : Ty} {t₁ t₂ : Γ ⊢ τ}
    (mtr mtr' : t₁ ⟶* t₂)
    (norm : Normal t₂) :
    mtr = mtr' :=
    match mtr, mtr' with
    | .refl _, .refl _ => rfl
    | .refl _, .trans _ tr' _ => Empty.elim (Normal.does_not_reduce norm tr')
    | .trans _ tr mtr, .refl _ => Empty.elim (Normal.does_not_reduce norm tr)
    | .trans _ tr mtr'', .trans _ tr' mtr''' => by
        have := Transition.deterministic tr tr'
        subst this
        rw [Transition.irrelevant tr tr', irrelevant' mtr'' mtr''' norm]

  unfold Typing.step_count
  
  let ⟨mtr₁, norm₁⟩ := t₁.weakly_normalizing
  let ⟨mtr₂, norm₂⟩ := t₂.weakly_normalizing

  cases mtr₁ with
  | refl => exact Empty.elim (Normal.does_not_reduce norm₁ tr₁)
  | trans _ tr₁' mtr₂' =>
      simp only
      conv => rhs; unfold Transitionᵣₜ.length

      revert mtr₂ mtr₂'
      have := Transition.deterministic tr₁ tr₁'
      subst this
      intro mtr₂' mtr₂

      have := Transitionᵣₜ.deterministic mtr₂ mtr₂' norm₁ norm₂
      subst this
      rw [irrelevant' mtr₂ mtr₂' norm₁, Nat.add_comm]
      exact Nat.lt_succ_self (Transitionᵣₜ.length mtr₂')

namespace Transitionᵣₜ

theorem step_count_decreases
  {Γ : Context} {τ : Ty} {t₁ t₂ : Γ ⊢ τ} (mtr : t₁ ⟶* t₂) :
  t₂.step_count <= t₁.step_count :=
  match mtr with
  | .refl _ => Nat.le_refl _
  | .trans _ tr mtr =>
      let lt := calc Typing.step_count t₂
        _ <= _ := mtr.step_count_decreases
        _ < _ := tr.step_count_decreases
      Nat.le_of_lt lt

theorem irrelevant
  {Γ : Context} {τ : Ty} {t₁ t₂ : Γ ⊢ τ}
  (mtr mtr' : t₁ ⟶* t₂) :
  mtr = mtr' :=
  match mtr, mtr' with
  | .refl _, .refl _ => rfl
  | .refl _, .trans t' tr' mtr' => by
      rename_i tₘ
      have lt :=
        calc Typing.step_count tₘ
          _ < _ := tr'.step_count_decreases
          _ <= _ := mtr'.step_count_decreases
      exact False.elim (Nat.lt_irrefl _ lt)
  | .trans _ tr mtr, .refl _ => by
      rename_i tₘ
      have lt :=
        calc Typing.step_count tₘ
          _ < _ := tr.step_count_decreases
          _ <= _ := mtr.step_count_decreases
      exact False.elim (Nat.lt_irrefl _ lt)
  | .trans _ tr mtr'', .trans _ tr' mtr''' => by
      have := Transition.deterministic tr tr'
      subst this
      rw [Transition.irrelevant tr tr', irrelevant mtr'' mtr''']

end Transitionᵣₜ

inductive StronglyNormalizing : {Γ : Context} → {τ : Ty} → (Γ ⊢ τ) → Type where
  | intro {Γ : Context} {τ : Ty} (t : Γ ⊢ τ) (h : (t' : Γ ⊢ τ) → (t ⟶ t') → StronglyNormalizing t') : StronglyNormalizing t

def Typing.strongly_normalizing
  {Γ : Context} {τ : Ty} (t : Γ ⊢ τ) :
  StronglyNormalizing t :=
  let h (t' : Γ ⊢ τ) (tr : t ⟶ t') : StronglyNormalizing t' := by
    have := tr.step_count_decreases
    exact strongly_normalizing t'
  
  StronglyNormalizing.intro t h

termination_by strongly_normalizing t => t.step_count
