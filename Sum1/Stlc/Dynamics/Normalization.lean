import Stlc.Dynamics.Normal
import Stlc.Dynamics.Progress
import Stlc.Dynamics.Transition
import Stlc.Statics

open Statics

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

-- Logical predicate
private def HereditarilyNormalizing {Γ : Context} {τ : Ty} (e : Γ ⊢ τ) : Type :=
  match τ with
  | .void => e ⇓
  | .sum τₗ τᵣ => Σ' (wn : e ⇓), (∀ {eₗ' : Γ ⊢ τₗ}, wn.e' = Expr.inl eₗ' → HereditarilyNormalizing eₗ') × (∀ {eᵣ' : Γ ⊢ τᵣ}, wn.e' = Expr.inr eᵣ' → HereditarilyNormalizing eᵣ')
  | .arrow τ _ => (e ⇓) × ∀ {e' : Γ ⊢ τ}, HereditarilyNormalizing e' → HereditarilyNormalizing (Expr.application e e')

namespace HereditarilyNormalizing

private def weakly_normalizing
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (hn : HereditarilyNormalizing e) :
  WeaklyNormalizing e :=
  match τ with
  | .void => hn
  | .sum _ _ => hn.1
  | .arrow _ _ => hn.1

private def forward_step
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ}
  (hn : HereditarilyNormalizing e)
  (tr : e ⟶ e') :
  HereditarilyNormalizing e' :=
  match τ with
  | .void => by
      let ⟨mtr, norm⟩ := hn
      cases mtr with
      | refl => exact Empty.elim (norm.does_not_reduce tr)
      | trans _ tr' mtr' =>
          rw [Transition.deterministic tr tr']
          exact ⟨mtr', norm⟩
  | .sum τₗ τᵣ => by
      let ⟨wn, preservesₗ, preservesᵣ⟩ := hn
      let ⟨mtr, norm⟩ := wn
      let wn'@⟨mtr', norm'⟩ := WeaklyNormalizing.forward_step wn tr
      let mtr' := 
        calc e
          _ ⟶ _ := tr
          _ ⟶* _ := mtr'

      have := Transitionᵣₜ.deterministic mtr mtr' norm norm'

      let preservesₗ {eₗ' : Γ ⊢ τₗ} (eq : wn'.e' = Expr.inl eₗ') : Dynamics.HereditarilyNormalizing eₗ'
      := by
        subst_vars
        exact preservesₗ (by simp_all)
      let preservesᵣ {eᵣ' : Γ ⊢ τᵣ} (eq : wn'.e' = Expr.inr eᵣ') : Dynamics.HereditarilyNormalizing eᵣ'
      := by
        subst_vars
        exact preservesᵣ (by simp_all)
      
      exact ⟨wn', preservesₗ, preservesᵣ⟩
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
  | .void => 
      let ⟨mtr, norm⟩ := hn
      ⟨Transitionᵣₜ.trans _ tr mtr, norm⟩
  | .sum τₗ τᵣ => by
      let ⟨wn, preservesₗ, preservesᵣ⟩ := hn
      let ⟨mtr, norm⟩ := wn
      let wn'@⟨mtr', norm'⟩ := WeaklyNormalizing.backward_step wn tr
      let mtr := 
        calc e
          _ ⟶ _ := tr
          _ ⟶* _ := mtr

      have := Transitionᵣₜ.deterministic mtr mtr' norm norm'

      let preservesₗ {eₗ' : Γ ⊢ τₗ} (eq : wn'.e' = Expr.inl eₗ') : Dynamics.HereditarilyNormalizing eₗ'
      := by
        subst_vars
        exact preservesₗ (by simp_all)
      let preservesᵣ {eᵣ' : Γ ⊢ τᵣ} (eq : wn'.e' = Expr.inr eᵣ') : Dynamics.HereditarilyNormalizing eᵣ'
      := by
        subst_vars
        exact preservesᵣ (by simp_all)
      
      exact ⟨wn', preservesₗ, preservesᵣ⟩
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
private inductive Elim (Γ : Context) where
  | application {τ : Ty} {e : Γ ⊢ τ} : (e ⇓) → Elim Γ

private def elim_ty {Γ : Context} : Elim Γ → Ty → Ty
  | @Elim.application _ τ' _ _, τ  => Ty.arrow τ' τ

private def elimᵣ_ty {Γ : Context} (exs : List (Elim Γ)) (τ : Ty) : Ty := List.foldr elim_ty τ exs

private theorem elim_tyᵣ_elim_ty_comm
  {Γ : Context}
  (τ : Ty) (ex : Elim Γ) :
  (exs : List (Elim Γ)) →
  elimᵣ_ty exs (elim_ty ex τ) = elimᵣ_ty (exs ++ [ex]) τ :=
by
  simp only [elimᵣ_ty, List.foldr_append, List.foldr, forall_const]

private def elim
  {Γ : Context} {τ : Ty} :
  (ex : Elim Γ) →
  (Γ ⊢ (elim_ty ex τ)) →
  Γ ⊢ τ
  | @Elim.application _ _ e' _, e => Expr.application e e'

private def elimᵣ
  {Γ : Context} {τ : Ty} :
  (exs : List (Elim Γ)) →
  (Γ ⊢ (elimᵣ_ty exs τ)) →
  Γ ⊢ τ
  | [], e => e
  | ex :: exs, e => elimᵣ exs (elim ex e)

private def elimᵣ_elim_comm
  {Γ : Context} {τ : Ty}
  (exs : List (Elim Γ)) (ex : Elim Γ)
  (e : Γ ⊢ (elimᵣ_ty (exs ++ [ex]) τ)) :
  elimᵣ (exs ++ [ex]) e = elim ex (elimᵣ exs (e.cast rfl (elim_tyᵣ_elim_ty_comm τ ex exs).symm)) :=
by
  match exs with
  | [] => rfl
  | ex :: exs =>
      unfold elimᵣ
      simp only [List.cons_append]
      rw [elimᵣ_elim_comm _ _ _]
      
      match ex with
      | .application _ => 
          simp only [elim, List.cons_append]
          rw [Expr.cast_application]
          rfl

private def elimᵣ_wn
  {Γ : Context} {τ : Ty}
  (exs : List (Elim Γ))
  {e : Γ ⊢ (elimᵣ_ty exs τ)}
  (wn : e ⇓) (wn_neut : Neutral wn.e') :
  (elimᵣ exs e) ⇓ :=
  match exs with
  | [] => wn
  | ex :: exs =>
      match ex with
      | @Elim.application _ _ e' wn' =>
          let wn : Expr.application e e' ⇓ :=
            ⟨
              calc Expr.application e e'
                _ ⟶* Expr.application wn.e' e' := Transitionᵣₜ.ξ_application₁ wn.normalizes.mtr
                _ ⟶* Expr.application wn.e' wn'.e' := Transitionᵣₜ.ξ_application₂ wn.normalizes.norm wn'.normalizes.mtr,
              (Neutral.application wn_neut wn'.normalizes.norm).normal
            ⟩
          elimᵣ_wn exs wn (Neutral.application wn_neut wn'.normalizes.norm)

private def elimᵣ_wn_neutral
  {Γ : Context} {τ : Ty}
  (exs : List (Elim Γ))
  {e : Γ ⊢ (elimᵣ_ty exs τ)}
  (wn : e ⇓) (wn_neut : Neutral wn.e')
  (h : (elimᵣ exs e) ⇓)
  (eq : h = elimᵣ_wn exs wn wn_neut) :
  Neutral h.e' :=
by
  match exs with
  | [] => subst_vars; exact wn_neut
  | ex :: exs =>
      match ex with
      | .application wn' =>
          subst_vars
          simp [elimᵣ_wn]
          apply elimᵣ_wn_neutral _ _ _ _ rfl

private def elimᵣ_hn
  {Γ : Context} {τ : Ty}
  (exs : List (Elim Γ)) {e : Γ ⊢ (elimᵣ_ty exs τ)}
  (neut : Neutral e) :
  HereditarilyNormalizing (elimᵣ exs e) :=
by
  let wn : e ⇓ := ⟨Transitionᵣₜ.refl _, neut.normal⟩
  let _wn := elimᵣ_wn exs wn neut
  have neut' := elimᵣ_wn_neutral exs wn neut _wn rfl

  cases τ with
  | void => exact _wn
  | sum τₗ τᵣ =>
      let preservesₗ {eₗ' : Γ ⊢ τₗ} (eq : _wn.e' = Expr.inl eₗ') : Dynamics.HereditarilyNormalizing eₗ'
      := by
        rw [eq] at neut'
        let ⟨mtr, norm⟩ := _wn
        subst_vars
        
        cases norm with
        | value val => exact Empty.elim (val.not_neutral neut')
        | neutral neut =>
            cases neut with
            | inl neut => exact elimᵣ_hn [] neut

      let preservesᵣ {eᵣ' : Γ ⊢ τᵣ} (eq : _wn.e' = Expr.inr eᵣ') : Dynamics.HereditarilyNormalizing eᵣ'
      := by
        rw [eq] at neut'
        let ⟨mtr, norm⟩ := _wn
        subst_vars
        
        cases norm with
        | value val => exact Empty.elim (val.not_neutral neut')
        | neutral neut =>
            cases neut with
            | inr neut => exact elimᵣ_hn [] neut
      exact ⟨_wn, preservesₗ, preservesᵣ⟩
  | arrow τ τ' =>
      let preserves {e' : Γ ⊢ τ} (hn : HereditarilyNormalizing e') : HereditarilyNormalizing (Expr.application (elimᵣ exs e) e') :=
      by
        let ex : Elim Γ := Elim.application hn.weakly_normalizing

        have eq : elimᵣ_ty exs (elim_ty ex τ') = elimᵣ_ty (exs ++ [ex]) τ' := by rw [elim_tyᵣ_elim_ty_comm]

        let h := @elimᵣ_hn _ _ (exs ++ [ex]) (e.cast rfl eq) (neut.cast rfl eq rfl)
        simp only [elimᵣ_elim_comm, Expr.cast_cast, Expr.cast_rfl_rfl] at h
        exact h
      
      exact ⟨_wn, preserves⟩

namespace Neutral

private def hereditarily_normalizing
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (neut : Neutral e) :
  HereditarilyNormalizing e :=
  match τ with
  | .void => ⟨Transitionᵣₜ.refl _, neut.normal⟩ 
  | .sum τₗ τᵣ => by
      let wn@⟨mtr, norm⟩ : WeaklyNormalizing e := ⟨Transitionᵣₜ.refl _, neut.normal⟩
      
      let preservesₗ {eₗ' : Γ ⊢ τₗ} (eq : wn.e' = Expr.inl eₗ') : Dynamics.HereditarilyNormalizing eₗ'
      := by 
        subst_vars
        cases mtr with
        | refl =>
            cases neut with
            | inl neut => exact hereditarily_normalizing neut
        | trans _ tr _ => exact Empty.elim (neut.does_not_reduce tr)
      
      let preservesᵣ {eᵣ' : Γ ⊢ τᵣ} (eq : wn.e' = Expr.inr eᵣ') : Dynamics.HereditarilyNormalizing eᵣ'
      := by 
        subst_vars
        cases mtr with
        | refl =>
            cases neut with
            | inr neut => exact hereditarily_normalizing neut
        | trans _ tr _ => exact Empty.elim (neut.does_not_reduce tr)
      
      exact ⟨wn, preservesₗ, preservesᵣ⟩
  | .arrow τ _ =>
      let preserves {e' : Γ ⊢ τ} (hn' : HereditarilyNormalizing e') : HereditarilyNormalizing (Expr.application e e') :=
        elimᵣ_hn [Elim.application hn'.weakly_normalizing] neut

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
  | .nullary_case e => by
      let hn := hereditarily_normalizing e hn_σ
      let ⟨mtr, norm⟩ := hn.weakly_normalizing
      
      cases norm with
      | value val => exact nomatch val
      | neutral neut =>
          rename_i e'
          let neut : Neutral (@Expr.nullary_case _ τ e') := Neutral.nullary_case neut
          exact HereditarilyNormalizing.backward_steps neut.hereditarily_normalizing
                                                       (Transitionᵣₜ.ξ_nullary_case mtr)
  | @Expr.inl _ τₗ τᵣ e =>
      let hn := hereditarily_normalizing e hn_σ
      let ⟨mtr, norm⟩ := hn.weakly_normalizing
      let wn := ⟨Transitionᵣₜ.ξ_inl mtr, Normal.inl norm⟩
      let preservesₗ {eₗ' : Δ ⊢ τₗ} (eq : wn.e' = Expr.inl eₗ') : HereditarilyNormalizing eₗ'
      := by
        simp only [Expr.inl.injEq] at eq
        subst_vars
        exact HereditarilyNormalizing.forward_steps hn mtr
      let preservesᵣ {eᵣ' : Δ ⊢ τᵣ} (eq : wn.e' = Expr.inr eᵣ') : HereditarilyNormalizing eᵣ'
      := by simp_all only

      ⟨wn, preservesₗ, preservesᵣ⟩
  | @Expr.inr _ τₗ τᵣ e =>
      let hn := hereditarily_normalizing e hn_σ
      let ⟨mtr, norm⟩ := hn.weakly_normalizing
      let wn := ⟨Transitionᵣₜ.ξ_inr mtr, Normal.inr norm⟩
      let preservesₗ {eₗ' : Δ ⊢ τₗ} (eq : wn.e' = Expr.inl eₗ') : HereditarilyNormalizing eₗ'
      := by simp_all only
      let preservesᵣ {eᵣ' : Δ ⊢ τᵣ} (eq : wn.e' = Expr.inr eᵣ') : HereditarilyNormalizing eᵣ'
      := by
        simp only [Expr.inr.injEq] at eq
        subst_vars
        exact HereditarilyNormalizing.forward_steps hn mtr

      ⟨wn, preservesₗ, preservesᵣ⟩
  | @Expr.binary_case _ _ τₗ τᵣ e eₗ eᵣ => by
      let hn@⟨⟨mtr, norm⟩, preservesₗ, preservesᵣ⟩ := hereditarily_normalizing e hn_σ

      cases norm with
      | neutral neut =>
          exact HereditarilyNormalizing.backward_steps (Neutral.binary_case neut).hereditarily_normalizing
                                                       (Transitionᵣₜ.ξ_binary_case mtr)
      | value val =>
          cases val with
          | inl val =>
              rename_i eₗ' _

              let σ' : Subst (τₗ :: Γ) Δ := Subst.cons eₗ' σ
              let hn_σ' : HereditarilyNormalizingSubst σ'
              | _, .here => preservesₗ rfl
              | _, .there a => hn_σ a
              let hnₗ := hereditarily_normalizing eₗ hn_σ'

              apply HereditarilyNormalizing.backward_steps hnₗ
              calc Expr.binary_case ((⟪ σ ⟫) e) ((⟪ σ.exts ⟫) eₗ) ((⟪ σ.exts ⟫) eᵣ)
                _ ⟶* _ := Transitionᵣₜ.ξ_binary_case mtr
                _ ⟶ _ := Transition.β_binary_caseₗ (by simp) val
          | inr val =>
              rename_i eᵣ' _

              let σ' : Subst (τᵣ :: Γ) Δ := Subst.cons eᵣ' σ
              let hn_σ' : HereditarilyNormalizingSubst σ'
              | _, .here => preservesᵣ rfl
              | _, .there a => hn_σ a
              let hnᵣ := hereditarily_normalizing eᵣ hn_σ'

              apply HereditarilyNormalizing.backward_steps hnᵣ
              calc Expr.binary_case ((⟪ σ ⟫) e) ((⟪ σ.exts ⟫) eₗ) ((⟪ σ.exts ⟫) eᵣ)
                _ ⟶* _ := Transitionᵣₜ.ξ_binary_case mtr
                _ ⟶ _ := Transition.β_binary_caseᵣ (by simp) val
  | @Expr.abstraction _ τ _ e =>
      let preserves {e' : Δ ⊢ τ} (hn' : HereditarilyNormalizing e') : HereditarilyNormalizing (Expr.application ((⟪ σ ⟫) (Expr.abstraction e)) e')
      := by
        let { e' := e'', normalizes := { mtr := mtr', norm := norm'' } } := hn'.weakly_normalizing
        let σ' : Subst (τ :: Γ) Δ := Subst.cons e'' σ
        let hn_σ' : HereditarilyNormalizingSubst σ'
        | _, .here => HereditarilyNormalizing.forward_steps hn' mtr'
        | _, .there a => hn_σ a

        apply HereditarilyNormalizing.backward_steps (hereditarily_normalizing e hn_σ')
        
        calc Expr.application (Expr.abstraction ((⟪ Subst.exts σ ⟫) e)) e'
          _ ⟶* Expr.application (Expr.abstraction ((⟪ Subst.exts σ ⟫) e)) e'' :=
            Transitionᵣₜ.ξ_application₂ Value.abstraction.normal mtr'
          _ ⟶ (⟪ λ a => (e'' •` σ) a ⟫) e := by
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

private def _root_.Statics.Subst.ids_hereditarily_normalizing
  {Γ : Context} : HereditarilyNormalizingSubst (@Subst.ids Γ)
  | _, a => Neutral.hereditarily_normalizing (Neutral.var a)

-- Finally, the result of weak normalization
def _root_.Statics.Expr.weakly_normalizing
  {Γ : Context} {τ : Ty}
  (e : Γ ⊢ τ) :
  WeaklyNormalizing e := by
  let hn := hereditarily_normalizing e Subst.ids_hereditarily_normalizing
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
