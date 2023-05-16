import Aesop

import T.Dynamics.Normal
import T.Dynamics.Progress
import T.Dynamics.Transition
import T.Statics

open Statics

-- Proof of weak normalization based on http://www.cs.cmu.edu/~rwh/courses/chtt/pdfs/kripke-steps.pdf
namespace Dynamics

structure NormalizesTo {Γ : Context} {τ : Ty} (e e' : Γ ⊢ τ) where
  mtr : e ⟶* e'
  norm : Normal e'

structure WeaklyNormalizing {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) where
  {e' : Γ ⊢ τ}
  normalizes : NormalizesTo e e'

notation:20 t " ⇓ " t' => NormalizesTo t t'
notation:20 t " ⇓" => WeaklyNormalizing t

structure TerminatesTo {Γ : Context} {τ : Ty} (e e' : Γ ⊢ τ) where
  mtr : e ⟶* e'
  norm : Value e'

structure Terminating {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) where
  {e' : Γ ⊢ τ}
  terminates : TerminatesTo e e'

structure Stuck {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) where
  norm : Normal e
  not_val : Value e → Empty

namespace Neutral

def stuck {Γ : Context} {τ : Ty} {e : Γ ⊢ τ} (neut : Neutral e) : Stuck e := ⟨neut.normal, neut.not_a_value⟩

end Neutral

def _root_.Statics.Expr.not_stuck {τ : Ty} (e : ⊢ τ) (stuck : Stuck e) : Empty :=
  let ⟨norm, not_val⟩ := stuck
  match e.progress with
  | .step tr => Empty.elim (Normal.does_not_reduce norm tr)
  | .done val => Empty.elim (not_val val)

namespace WeaklyNormalizing

def forward_step
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ} :
  (e ⇓) →
  (e ⟶ e') →
  (e' ⇓)
  | ⟨.trans _ tr' tr'',  norm''⟩, tr => by
      simp only [Transition.deterministic tr tr']
      exact ⟨tr'', norm''⟩
  | ⟨.refl _, norm''⟩, tr => Empty.elim (norm''.does_not_reduce tr)

def forward_steps
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ}
  (wn : e ⇓) :
  (e ⟶* e') →
  (e' ⇓)
  | .refl _ => wn
  | .trans _ tr mtr => forward_steps (forward_step wn tr) mtr

def backward_step
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ} :
  (e' ⇓) →
  (e ⟶ e') →
  (e ⇓)
  | ⟨mtr, norm''⟩, tr => ⟨Transitionᵣₜ.trans _ tr mtr, norm''⟩

def backward_steps
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ}
  (wn : e' ⇓) :
  (e ⟶* e') →
  (e ⇓)
  | .refl _ => wn
  | .trans _ tr mtr => backward_step (backward_steps wn mtr) tr

end WeaklyNormalizing

private def HereditarilyNormalizing {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) : Type :=
  match τ with
  | .nat => e ⇓
  | .arrow τ _ => (e ⇓) × ∀ {e' : Γ ⊢ τ}, HereditarilyNormalizing e' → HereditarilyNormalizing (Expr.application e e')

namespace HereditarilyNormalizing

private def weakly_normalizing
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (hn : HereditarilyNormalizing e) :
  WeaklyNormalizing e :=
  match τ with
  | .nat => hn
  | .arrow _ _ => hn.1

private def forward_step
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ}
  (hn : HereditarilyNormalizing e)
  (tr : e ⟶ e') :
  HereditarilyNormalizing e' :=
  match τ with
  | .nat => WeaklyNormalizing.forward_step hn tr
  | .arrow τ _ =>
      let ⟨wn, preserves⟩ := hn
      let preserves {e'' : Γ ⊢ τ} (hn'' : HereditarilyNormalizing e'') : HereditarilyNormalizing (Expr.application e' e'') :=
        forward_step (preserves hn'') (Transition.ξ_application₁ tr)

      ⟨WeaklyNormalizing.forward_step wn tr, preserves⟩

private def forward_steps
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ}
  (hn : HereditarilyNormalizing e) :
  (e ⟶* e') →
  HereditarilyNormalizing e'
  | .refl _ => hn
  | .trans _ tr mtr => forward_steps (forward_step hn tr) mtr

private def backward_step
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ}
  (hn : HereditarilyNormalizing e')
  (tr : e ⟶ e') :
  HereditarilyNormalizing e :=
  match τ with
  | .nat => WeaklyNormalizing.backward_step hn tr
  | .arrow τ _ =>
      let ⟨wn, preserves⟩ := hn

      let preserves {e'' : Γ ⊢ τ} (hn'' : HereditarilyNormalizing e'') : HereditarilyNormalizing (Expr.application e e'') :=
        backward_step (preserves hn'') (Transition.ξ_application₁ tr)

      ⟨WeaklyNormalizing.backward_step wn tr, preserves⟩

private def backward_steps
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ}
  (hn : HereditarilyNormalizing e') :
  (e ⟶* e') →
  HereditarilyNormalizing e
  | .refl _ => hn
  | .trans _ tr mtr => backward_step (backward_steps hn mtr) tr

end HereditarilyNormalizing

private abbrev HereditarilyNormalizingSubst
  {Γ Δ : Context} (σ : Subst Γ Δ) :=
  ∀ {τ : Ty}, (a : Γ ∋ τ) → HereditarilyNormalizing (σ a)

-- Prove that all neutral terms are hereditarily normalizing.
private structure WnExpr (Γ : Context) where
  {τ : Ty}
  {e : Γ ⊢ τ}
  wn : WeaklyNormalizing e

private abbrev arrowᵣ {Γ : Context} (τ : Ty) (exs : List (WnExpr Γ)) := Ty.arrowᵣ τ (List.map WnExpr.τ exs)

private def applicationᵣ
  {Γ : Context} {τ : Ty} :
  (exs : List (WnExpr Γ)) →
  (Γ ⊢ (arrowᵣ τ exs)) →
  Γ ⊢ τ
  | [], e => e
  | ex :: exs, e => applicationᵣ exs (Expr.application e ex.e)

private def comm_lemma
  {Γ : Context}
  (τ : Ty) (exs : List (WnExpr Γ)) (ex : WnExpr Γ) :
  Ty.arrowᵣ τ (List.map WnExpr.τ (exs ++ [ex])) = Ty.arrowᵣ (Ty.arrow ex.τ τ) (List.map WnExpr.τ exs) :=
by
  rw [Ty.arrowᵣ_arrow_comm]
  have : List.map WnExpr.τ (exs ++ [ex]) = List.map WnExpr.τ exs ++ [ex.τ] := by simp only [List.map_append, List.map]
  rw [this]

private def applicationᵣ_application_comm
  {Γ : Context} {τ : Ty}
  (exs : List (WnExpr Γ)) (ex : WnExpr Γ)
  (e : Γ ⊢ (Ty.arrowᵣ τ (List.map WnExpr.τ (exs ++ [ex])))) :
  applicationᵣ (exs ++ [ex]) e = Expr.application (applicationᵣ exs (e.cast rfl (comm_lemma τ exs ex))) ex.e :=
by
  match exs with
  | [] => rfl
  | _ :: exs =>
      unfold applicationᵣ
      simp only [List.cons_append]
      rw [applicationᵣ_application_comm _ _ _, Expr.cast_application]
      . rfl
      . rfl

private def applicationᵣ_wn
  {Γ : Context} {τ : Ty}
  (exs : List (WnExpr Γ))
  (e : Γ ⊢ (arrowᵣ τ exs))
  (wn : e ⇓) (wn_neut : Neutral wn.e') :
  (applicationᵣ exs e) ⇓ :=
  match exs with
  | [] => wn
  | ex :: exs =>
      let wn : Expr.application e ex.e ⇓ :=
        ⟨
          calc Expr.application e ex.e
            _ ⟶* Expr.application wn.e' ex.e := Transitionᵣₜ.ξ_application₁ wn.normalizes.mtr
            _ ⟶* Expr.application wn.e' ex.wn.e' := Transitionᵣₜ.ξ_application₂ wn.normalizes.norm ex.wn.normalizes.mtr,
          (Neutral.application wn_neut ex.wn.normalizes.norm).normal
        ⟩
      applicationᵣ_wn exs (Expr.application e ex.e) wn (Neutral.application wn_neut ex.wn.normalizes.norm)

private def applicationᵣ_hn
  {Γ : Context} {τ : Ty}
  (exs : List (WnExpr Γ)) {e : Γ ⊢ arrowᵣ τ exs}
  (neut : Neutral e) :
  HereditarilyNormalizing (applicationᵣ exs e) := by
  let _wn := applicationᵣ_wn exs e ⟨Transitionᵣₜ.refl _, neut.normal⟩ neut
  cases τ with
  | nat => exact _wn
  | arrow τ τ' =>
      let preserves {e' : Γ ⊢ τ} (hn : HereditarilyNormalizing e') : HereditarilyNormalizing (Expr.application (applicationᵣ exs e) e') :=
      by
        let ex : WnExpr Γ := ⟨hn.weakly_normalizing⟩
        
        have eq : arrowᵣ (Ty.arrow τ τ') exs = arrowᵣ τ' (exs ++ [ex]) := by
          unfold arrowᵣ
          rw [Ty.arrowᵣ_arrow_comm]
          simp only [List.map_append, List.map]

        let h := @applicationᵣ_hn _ _ (exs ++ [ex]) (e.cast rfl eq) (neut.cast rfl eq rfl)
        simp only [applicationᵣ_application_comm, Expr.cast_cast, Expr.cast_rfl_rfl] at h
        exact h

      exact ⟨_wn, preserves⟩

namespace Neutral

-- Logical predicate
private def hereditarily_normalizing
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (neut : Neutral e) :
  HereditarilyNormalizing e :=
  match τ with
  | .nat => ⟨Transitionᵣₜ.refl _, neut.normal⟩
  | .arrow τ _ =>
      let preserves {e' : Γ ⊢ τ} (hn' : HereditarilyNormalizing e') : HereditarilyNormalizing (Expr.application e e') :=
        applicationᵣ_hn [⟨hn'.weakly_normalizing⟩] neut

      ⟨⟨Transitionᵣₜ.refl _, neut.normal⟩, preserves⟩

end Neutral

-- Main theorem
private def hereditarily_normalizing
  {Γ Δ : Context} {τ : Ty} {σ : Subst Γ Δ}
  (e : Γ ⊢ τ)
  (hn_σ : HereditarilyNormalizingSubst σ) :
  HereditarilyNormalizing ((⟪ σ ⟫) e) :=
  match e with
  | .var a => hn_σ a
  | .zero => ⟨Transitionᵣₜ.refl _, Value.zero.normal⟩
  | .succ e => 
      let ⟨mtr, norm⟩ := hereditarily_normalizing e hn_σ
      ⟨Transitionᵣₜ.ξ_succ mtr, Normal.succ norm⟩
  | .recursor e e₀ eₛ => by
      let ⟨mtr, norm⟩ := hereditarily_normalizing e hn_σ

      cases norm with
      | neutral neut =>
          exact HereditarilyNormalizing.backward_steps (Neutral.recursor neut).hereditarily_normalizing
                                                       (Transitionᵣₜ.ξ_recursor mtr)
      | value val =>
          let hn₀ := hereditarily_normalizing e₀ hn_σ
          let hnₛ (σ') : HereditarilyNormalizingSubst σ' → _ := λ hn_σ' => @hereditarily_normalizing _ Δ _ _ eₛ hn_σ'

          -- Induction principle for natural numbers
          let rec lemma
            {e : Δ ⊢ Ty.nat} (val : Value e) :
            HereditarilyNormalizing (Expr.recursor e ((⟪ σ ⟫) e₀) ((⟪ Subst.exts σ.exts ⟫) eₛ)) :=
          by
            cases val with
            | zero =>
              let mtr :=
                calc Expr.recursor Expr.zero ((⟪ σ ⟫) e₀) ((⟪ Subst.exts σ.exts ⟫) eₛ)
                  _ ⟶ (⟪ σ ⟫) e₀ := Transition.β_recursor₀
              exact HereditarilyNormalizing.backward_step hn₀ mtr
            | succ val =>
                rename_i e'
                let mtr :=
                  calc Expr.recursor (Expr.succ e') ((⟪ σ ⟫) e₀) ((⟪ Subst.exts σ.exts ⟫) eₛ)
                    _ ⟶ _ := Transition.β_recursorₛ rfl val
                let σ' : Subst (τ :: Ty.nat :: Γ) Δ := (Expr.recursor e' (e₀.subst σ) (eₛ.subst (Subst.exts σ.exts))) • e' • σ
                let hn_σ' : HereditarilyNormalizingSubst σ'
                | _, .here => lemma val
                | _, .there .here => ⟨Transitionᵣₜ.refl _, val.normal⟩
                | _, .there (.there a) => hn_σ a
                let hnₛ := hnₛ _ hn_σ'

                simp only [Subst.exts_cons_shift, Subst.subst_dist, Subst.subst_assoc]
                simp only [Subst.exts_cons_shift, Subst.subst_dist, Subst.subst_assoc] at hnₛ
                simp only [
                  Subst.exts_cons_shift, Subst.subst_dist, Subst.subst_assoc, Subst.subst_subst, Subst.subst_head,
                  Subst.subst_tail, Subst.subst_id_right
                ] at mtr

                exact HereditarilyNormalizing.backward_step hnₛ mtr

          exact HereditarilyNormalizing.backward_steps (lemma val) (Transitionᵣₜ.ξ_recursor mtr)
  | @Expr.abstraction _ τ _ e =>
      let preserves {e' : Δ ⊢ τ} (hn' : HereditarilyNormalizing e') : HereditarilyNormalizing (Expr.application ((⟪ σ ⟫) (Expr.abstraction e)) e') := by
        let { e' := e'', normalizes := { mtr := mtr', norm := norm'' } } := hn'.weakly_normalizing
        let σ' : Subst (τ :: Γ) Δ := Subst.cons e'' σ
        let hn_σ' : HereditarilyNormalizingSubst σ'
        | _, .here => HereditarilyNormalizing.forward_steps hn' mtr'
        | _, .there a => hn_σ a

        apply HereditarilyNormalizing.backward_steps (hereditarily_normalizing e hn_σ')
        
        calc Expr.application (Expr.abstraction ((⟪ Subst.exts σ ⟫) e)) e'
          _ ⟶* Expr.application (Expr.abstraction ((⟪ Subst.exts σ ⟫) e)) e'' :=
            Transitionᵣₜ.ξ_application₂ Value.abstraction.normal mtr'
          _ ⟶ (⟪ λ a => (e'' • σ) a ⟫) e := by
            apply Transition.β_application
            . simp only [
                Subst.exts_cons_shift, Subst.subst_subst, Subst.subst_zero_cons_ids, Subst.subst_dist,
                Subst.subst_head, Subst.subst_assoc, Subst.subst_tail, Subst.subst_id_right
              ]
            . exact norm''
      ⟨⟨Transitionᵣₜ.refl _, Value.abstraction.normal⟩, preserves⟩
  | .application e₁ e₂ =>
      let ⟨_, preserves⟩ := hereditarily_normalizing e₁ hn_σ
      let hn₂ := hereditarily_normalizing e₂ hn_σ
      preserves hn₂

private def _root_.Statics.Subst.hereditarily_normalizing
  {Γ : Context} : HereditarilyNormalizingSubst (@Subst.ids Γ)
  | _, a => Neutral.hereditarily_normalizing (Neutral.var a)

-- Finally, the final result of weak normalization
def _root_.Statics.Expr.weakly_normalizing
  {Γ : Context} {τ : Ty}
  (e : Γ ⊢ τ) :
  WeaklyNormalizing e := by
  let hn := hereditarily_normalizing e Subst.hereditarily_normalizing
  simp only [Subst.subst_id, id_eq] at hn
  exact hn.weakly_normalizing

-- Prove the weaker property of terminating for closed expressions.
def _root_.Statics.Expr.terminating
  {τ : Ty}
  (e : ⊢ τ) :
  Terminating e :=
  let ⟨mtr, norm⟩ := e.weakly_normalizing

  match norm with
  | .neutral neut => Empty.elim neut.not_closed
  | .value val => ⟨mtr, val⟩

def _root_.Statics.Expr.normal
  {Γ : Context} {τ : Ty}
  (e : Γ ⊢ τ) :
  Γ ⊢ τ := e.weakly_normalizing.e'

@[simp]
theorem _root_.Statics.Expr.normal_idempotent
  {Γ : Context} {τ : Ty}
  (e : Γ ⊢ τ) :
  e.normal.normal = e.normal := by
  unfold Expr.normal
  
  let { e', normalizes := ⟨_, norm⟩ } := e.weakly_normalizing
  let ⟨mtr', _⟩ := e'.weakly_normalizing
  simp only

  match mtr' with
  | .refl _ => rfl
  | .trans _ tr _ => exact Empty.elim (Normal.does_not_reduce norm tr)

def _root_.Statics.Expr.step_count
  {Γ : Context} {τ : Ty}
  (e : Γ ⊢ τ) : Nat := e.weakly_normalizing.normalizes.mtr.length

theorem Transition.step_count_decreases
  {Γ : Context} {τ : Ty} {e₁ e₂ : Γ ⊢ τ} (tr₁ : e₁ ⟶ e₂) :
  e₂.step_count < e₁.step_count := by
  let rec irrelevant'
    {Γ : Context} {τ : Ty} {e₁ e₂ : Γ ⊢ τ}
    (mtr mtr' : e₁ ⟶* e₂)
    (norm : Normal e₂) :
    mtr = mtr' :=
    match mtr, mtr' with
    | .refl _, .refl _ => rfl
    | .refl _, .trans _ tr' _ => Empty.elim (Normal.does_not_reduce norm tr')
    | .trans _ tr mtr, .refl _ => Empty.elim (Normal.does_not_reduce norm tr)
    | .trans _ tr mtr'', .trans _ tr' mtr''' => by
        have := Transition.deterministic tr tr'
        subst this
        rw [Transition.irrelevant tr tr', irrelevant' mtr'' mtr''' norm]

  unfold Expr.step_count
  
  let ⟨mtr₁, norm₁⟩ := e₁.weakly_normalizing
  let ⟨mtr₂, norm₂⟩ := e₂.weakly_normalizing

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
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ} (mtr : e ⟶* e') :
  e'.step_count <= e.step_count :=
  match mtr with
  | .refl _ => Nat.le_refl _
  | .trans _ tr mtr =>
      let lt := calc Expr.step_count e'
        _ <= _ := mtr.step_count_decreases
        _ < _ := tr.step_count_decreases
      Nat.le_of_lt lt

theorem irrelevant
  {Γ : Context} {τ : Ty} {t₁ t₂ : Γ ⊢ τ}
  (mtr mtr' : t₁ ⟶* t₂) :
  mtr = mtr' :=
  match mtr, mtr' with
  | .refl _, .refl _ => rfl
  | .refl _, .trans _ tr' mtr' => by
      rename_i eₘ
      have lt :=
        calc Expr.step_count eₘ
          _ < _ := tr'.step_count_decreases
          _ <= _ := mtr'.step_count_decreases
      exact False.elim (Nat.lt_irrefl _ lt)
  | .trans _ tr mtr, .refl _ => by
      rename_i eₘ
      have lt :=
        calc Expr.step_count eₘ
          _ < _ := tr.step_count_decreases
          _ <= _ := mtr.step_count_decreases
      exact False.elim (Nat.lt_irrefl _ lt)
  | .trans _ tr mtr'', .trans _ tr' mtr''' => by
      have := Transition.deterministic tr tr'
      subst this
      rw [Transition.irrelevant tr tr', irrelevant mtr'' mtr''']

end Transitionᵣₜ

inductive StronglyNormalizing : {Γ : Context} → {τ : Ty} → (Γ ⊢ τ) → Type where
  | intro {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) (h : (e' : Γ ⊢ τ) → (e ⟶ e') → StronglyNormalizing e') : StronglyNormalizing e

def _root_.Statics.Expr.strongly_normalizing
  {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) :
  StronglyNormalizing e :=
  let h (e' : Γ ⊢ τ) (tr : e ⟶ e') : StronglyNormalizing e' := by
    have := tr.step_count_decreases
    exact strongly_normalizing e'
  
  StronglyNormalizing.intro e h

termination_by strongly_normalizing e => e.step_count
