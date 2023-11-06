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
  | .unit => e ⇓
  | .prod _ _ => (e ⇓) × HereditarilyNormalizing (Expr.projₗ e) × HereditarilyNormalizing (Expr.projᵣ e)
  | .void => e ⇓
  | .sum τₗ τᵣ => Σ' (wn : e ⇓), (∀ {eₗ' : Γ ⊢ τₗ}, wn.e' = Expr.inₗ eₗ' → HereditarilyNormalizing eₗ') × (∀ {eᵣ' : Γ ⊢ τᵣ}, wn.e' = Expr.inᵣ eᵣ' → HereditarilyNormalizing eᵣ')
  | .arrow τ _ => (e ⇓) × ∀ {e' : Γ ⊢ τ}, HereditarilyNormalizing e' → HereditarilyNormalizing (Expr.application e e')

namespace HereditarilyNormalizing

private def weakly_normalizing
  {Γ : Context} {τ : Ty} {e : Γ ⊢ τ}
  (hn : HereditarilyNormalizing e) :
  WeaklyNormalizing e :=
  match τ with
  | .unit => hn
  | .prod _ _ => hn.1
  | .void => hn
  | .sum _ _ => hn.1
  | .arrow _ _ => hn.1

private def forward_step
  {Γ : Context} {τ : Ty} {e e' : Γ ⊢ τ}
  (hn : HereditarilyNormalizing e)
  (tr : e ⟶ e') :
  HereditarilyNormalizing e' :=
  match τ with
  | .unit => WeaklyNormalizing.forward_step hn tr
  | .prod _ _ =>
      let ⟨wn, hn₁, hn₂⟩ := hn
      ⟨WeaklyNormalizing.forward_step wn tr, forward_step hn₁ (Transition.ξ_projₗ tr), forward_step hn₂ (Transition.ξ_projᵣ tr)⟩
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

      let preservesₗ {eₗ' : Γ ⊢ τₗ} (eq : wn'.e' = Expr.inₗ eₗ') : Dynamics.HereditarilyNormalizing eₗ'
      := by
        subst_vars
        exact preservesₗ (by simp_all)
      let preservesᵣ {eᵣ' : Γ ⊢ τᵣ} (eq : wn'.e' = Expr.inᵣ eᵣ') : Dynamics.HereditarilyNormalizing eᵣ'
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
  | .unit => WeaklyNormalizing.backward_step hn tr
  | .prod _ _ =>
      let ⟨wn, hn₁, hn₂⟩ := hn
      ⟨WeaklyNormalizing.backward_step wn tr, backward_step hn₁ (Transition.ξ_projₗ tr), backward_step hn₂ (Transition.ξ_projᵣ tr)⟩
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

      let preservesₗ {eₗ' : Γ ⊢ τₗ} (eq : wn'.e' = Expr.inₗ eₗ') : Dynamics.HereditarilyNormalizing eₗ'
      := by
        subst_vars
        exact preservesₗ (by simp_all)
      let preservesᵣ {eᵣ' : Γ ⊢ τᵣ} (eq : wn'.e' = Expr.inᵣ eᵣ') : Dynamics.HereditarilyNormalizing eᵣ'
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
  | projₗ : Ty → Elim Γ
  | projᵣ : Ty → Elim Γ
  | application {τ : Ty} {e : Γ ⊢ τ} : (e ⇓) → Elim Γ

private def elim_ty {Γ : Context} : Elim Γ → Ty → Ty
  | .projₗ τ', τ => Ty.prod τ τ'
  | .projᵣ τ', τ => Ty.prod τ' τ
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
  | .projₗ _, e => Expr.projₗ e
  | .projᵣ _, e => Expr.projᵣ e
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
      | .projₗ _ => simp only [elim, List.cons_append, Expr.cast_projₗ]
      | .projᵣ _ => simp only [elim, List.cons_append, Expr.cast_projᵣ]
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
      | .projₗ _ =>
          let wn : Expr.projₗ e ⇓ :=
            ⟨
              Transitionᵣₜ.ξ_projₗ wn.normalizes.mtr,
              (Neutral.projₗ wn_neut).normal
            ⟩
          elimᵣ_wn exs wn (Neutral.projₗ wn_neut)
      | .projᵣ _ =>
          let wn : Expr.projᵣ e ⇓ :=
            ⟨
              Transitionᵣₜ.ξ_projᵣ wn.normalizes.mtr,
              (Neutral.projᵣ wn_neut).normal
            ⟩
          elimᵣ_wn exs wn (Neutral.projᵣ wn_neut)
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
      | .projₗ _ =>
          subst_vars
          simp [elimᵣ_wn]
          apply elimᵣ_wn_neutral _ _ _ _ rfl
      | .projᵣ _ =>
          subst_vars
          simp [elimᵣ_wn]
          apply elimᵣ_wn_neutral _ _ _ _ rfl
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
  | unit => exact _wn
  | prod τₗ τᵣ =>
      unfold HereditarilyNormalizing
      let exₗ : Elim Γ := Elim.projₗ τᵣ
      let exᵣ : Elim Γ := Elim.projᵣ τₗ

      have eqₗ : elimᵣ_ty exs (elim_ty exₗ τₗ) = elimᵣ_ty (exs ++ [exₗ]) τₗ := by rw [elim_tyᵣ_elim_ty_comm]
      have eqᵣ : elimᵣ_ty exs (elim_ty exᵣ τᵣ) = elimᵣ_ty (exs ++ [exᵣ]) τᵣ := by rw [elim_tyᵣ_elim_ty_comm]

      let hnₗ := @elimᵣ_hn _ _ (exs ++ [exₗ]) (e.cast rfl eqₗ) (neut.cast rfl eqₗ rfl)
      let hnᵣ := @elimᵣ_hn _ _ (exs ++ [exᵣ]) (e.cast rfl eqᵣ) (neut.cast rfl eqᵣ rfl)

      simp only [elimᵣ_elim_comm, Expr.cast_cast, Expr.cast_rfl_rfl] at hnₗ
      simp only [elimᵣ_elim_comm, Expr.cast_cast, Expr.cast_rfl_rfl] at hnᵣ

      exact ⟨_wn, hnₗ, hnᵣ⟩
  | void => exact _wn
  | sum τₗ τᵣ =>
      let preservesₗ {eₗ' : Γ ⊢ τₗ} (eq : _wn.e' = Expr.inₗ eₗ') : Dynamics.HereditarilyNormalizing eₗ'
      := by
        rw [eq] at neut'
        let ⟨mtr, norm⟩ := _wn
        subst_vars

        cases norm with
        | value val => exact Empty.elim (val.not_neutral neut')
        | neutral neut =>
            cases neut with
            | inₗ neut => exact elimᵣ_hn [] neut

      let preservesᵣ {eᵣ' : Γ ⊢ τᵣ} (eq : _wn.e' = Expr.inᵣ eᵣ') : Dynamics.HereditarilyNormalizing eᵣ'
      := by
        rw [eq] at neut'
        let ⟨mtr, norm⟩ := _wn
        subst_vars

        cases norm with
        | value val => exact Empty.elim (val.not_neutral neut')
        | neutral neut =>
            cases neut with
            | inᵣ neut => exact elimᵣ_hn [] neut
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
  | .unit => ⟨Transitionᵣₜ.refl _, neut.normal⟩
  | .prod τₗ τᵣ => ⟨⟨Transitionᵣₜ.refl _, neut.normal⟩, elimᵣ_hn [Elim.projₗ τᵣ] neut, elimᵣ_hn [Elim.projᵣ τₗ] neut⟩
  | .void => ⟨Transitionᵣₜ.refl _, neut.normal⟩
  | .sum τₗ τᵣ => by
      let wn@⟨mtr, norm⟩ : WeaklyNormalizing e := ⟨Transitionᵣₜ.refl _, neut.normal⟩

      let preservesₗ {eₗ' : Γ ⊢ τₗ} (eq : wn.e' = Expr.inₗ eₗ') : Dynamics.HereditarilyNormalizing eₗ'
      := by
        subst_vars
        cases mtr with
        | refl =>
            cases neut with
            | inₗ neut => exact hereditarily_normalizing neut
        | trans _ tr _ => exact Empty.elim (neut.does_not_reduce tr)

      let preservesᵣ {eᵣ' : Γ ⊢ τᵣ} (eq : wn.e' = Expr.inᵣ eᵣ') : Dynamics.HereditarilyNormalizing eᵣ'
      := by
        subst_vars
        cases mtr with
        | refl =>
            cases neut with
            | inᵣ neut => exact hereditarily_normalizing neut
        | trans _ tr _ => exact Empty.elim (neut.does_not_reduce tr)

      exact ⟨wn, preservesₗ, preservesᵣ⟩
  | .arrow τ _ =>
      let preserves {e' : Γ ⊢ τ} (hn' : HereditarilyNormalizing e') : HereditarilyNormalizing (Expr.application e e') :=
        elimᵣ_hn [Elim.application hn'.weakly_normalizing] neut

      ⟨⟨Transitionᵣₜ.refl _, neut.normal⟩, preserves⟩

end Neutral


private def pair_hn
  {Γ : Context} {τₗ τᵣ : Ty} {eₗ : Γ ⊢ τₗ} {eᵣ : Γ ⊢ τᵣ}
  (hnₗ : HereditarilyNormalizing eₗ) (hnᵣ : HereditarilyNormalizing eᵣ) :
  HereditarilyNormalizing (Expr.pair eₗ eᵣ) :=
  let ⟨mtrₗ, normₗ⟩ := hnₗ.weakly_normalizing
  let ⟨mtrᵣ, normᵣ⟩ := hnᵣ.weakly_normalizing

  match normₗ, normᵣ with
  | .neutral neutₗ, normᵣ =>
      let wn : Expr.pair eₗ eᵣ ⇓ :=
        ⟨
          calc _
            _ ⟶* _ := Transitionᵣₜ.ξ_pairₗ mtrₗ
            _ ⟶* _ := Transitionᵣₜ.ξ_pairᵣ normₗ mtrᵣ,
          (Neutral.pairₗ neutₗ normᵣ).normal
        ⟩
      let hnₗ' :=
          let mtr :=
            calc _
              _ ⟶* _ := Transitionᵣₜ.ξ_projₗ (Transitionᵣₜ.ξ_pairₗ mtrₗ)
              _ ⟶* _ := Transitionᵣₜ.ξ_projₗ (Transitionᵣₜ.ξ_pairᵣ normₗ mtrᵣ)

          HereditarilyNormalizing.backward_steps (Neutral.projₗ (Neutral.pairₗ neutₗ normᵣ)).hereditarily_normalizing mtr
      let hnᵣ' :=
          let mtr :=
            calc _
              _ ⟶* _ := Transitionᵣₜ.ξ_projᵣ (Transitionᵣₜ.ξ_pairₗ mtrₗ)
              _ ⟶* _ := Transitionᵣₜ.ξ_projᵣ (Transitionᵣₜ.ξ_pairᵣ normₗ mtrᵣ)

          HereditarilyNormalizing.backward_steps (Neutral.projᵣ (Neutral.pairₗ neutₗ normᵣ)).hereditarily_normalizing mtr

      ⟨wn, hnₗ', hnᵣ'⟩
  | .value valₗ, .neutral neutᵣ =>
      let wn : Expr.pair eₗ eᵣ ⇓ :=
        ⟨
          calc _
            _ ⟶* _ := Transitionᵣₜ.ξ_pairₗ mtrₗ
            _ ⟶* _ := Transitionᵣₜ.ξ_pairᵣ normₗ mtrᵣ,
          (Neutral.pairᵣ valₗ neutᵣ).normal
        ⟩
      let hnₗ' :=
          let mtr :=
            calc _
              _ ⟶* _ := Transitionᵣₜ.ξ_projₗ (Transitionᵣₜ.ξ_pairₗ mtrₗ)
              _ ⟶* _ := Transitionᵣₜ.ξ_projₗ (Transitionᵣₜ.ξ_pairᵣ normₗ mtrᵣ)

          HereditarilyNormalizing.backward_steps (Neutral.projₗ (Neutral.pairᵣ valₗ neutᵣ)).hereditarily_normalizing mtr
      let hnᵣ' :=
          let mtr :=
            calc _
              _ ⟶* _ := Transitionᵣₜ.ξ_projᵣ (Transitionᵣₜ.ξ_pairₗ mtrₗ)
              _ ⟶* _ := Transitionᵣₜ.ξ_projᵣ (Transitionᵣₜ.ξ_pairᵣ normₗ mtrᵣ)

          HereditarilyNormalizing.backward_steps (Neutral.projᵣ (Neutral.pairᵣ valₗ neutᵣ)).hereditarily_normalizing mtr

      ⟨wn, hnₗ', hnᵣ'⟩
  | .value valₗ, .value valᵣ =>
      let wn : Expr.pair eₗ eᵣ ⇓ :=
        ⟨
          calc _
            _ ⟶* _ := Transitionᵣₜ.ξ_pairₗ mtrₗ
            _ ⟶* _ := Transitionᵣₜ.ξ_pairᵣ normₗ mtrᵣ,
          (Value.pair valₗ valᵣ).normal
        ⟩
      let hnₗ' :=
          let mtr :=
            calc _
              _ ⟶* _ := Transitionᵣₜ.ξ_projₗ (Transitionᵣₜ.ξ_pairₗ mtrₗ)
              _ ⟶* _ := Transitionᵣₜ.ξ_projₗ (Transitionᵣₜ.ξ_pairᵣ normₗ mtrᵣ)
              _ ⟶ _ := Transition.β_projₗ valₗ valᵣ

          HereditarilyNormalizing.backward_steps (HereditarilyNormalizing.forward_steps hnₗ mtrₗ) mtr
      let hnᵣ' :=
          let mtr :=
            calc _
              _ ⟶* _ := Transitionᵣₜ.ξ_projᵣ (Transitionᵣₜ.ξ_pairₗ mtrₗ)
              _ ⟶* _ := Transitionᵣₜ.ξ_projᵣ (Transitionᵣₜ.ξ_pairᵣ normₗ mtrᵣ)
              _ ⟶ _ := Transition.β_projᵣ valₗ valᵣ

          HereditarilyNormalizing.backward_steps (HereditarilyNormalizing.forward_steps hnᵣ mtrᵣ) mtr

      ⟨wn, hnₗ', hnᵣ'⟩

private def nullary_case_hn
  {Γ : Context} {τ : Ty} {e : Γ ⊢ Ty.void}
  (hn : HereditarilyNormalizing e) :
  HereditarilyNormalizing (@Expr.nullary_case _ τ e) :=
  let ⟨mtr, norm⟩ := hn.weakly_normalizing

  match norm with
  | .value val => nomatch val
  | .neutral neut =>
      let neut : Neutral (@Expr.nullary_case _ τ _) := Neutral.nullary_case neut
      HereditarilyNormalizing.backward_steps neut.hereditarily_normalizing (Transitionᵣₜ.ξ_nullary_case mtr)

private def inₗ_hn
  {Γ : Context} {τₗ τᵣ : Ty} {eₗ : Γ ⊢ τₗ}
  (hnₗ : HereditarilyNormalizing eₗ) :
  HereditarilyNormalizing (@Expr.inₗ _ τₗ τᵣ eₗ) :=
  let ⟨mtr, norm⟩ := hnₗ.weakly_normalizing
  let wn := ⟨Transitionᵣₜ.ξ_inₗ mtr, Normal.inₗ norm⟩
  let preservesₗ {eₗ' : Γ ⊢ τₗ} (eq : wn.e' = Expr.inₗ eₗ') : HereditarilyNormalizing eₗ'
  := by
    simp only [Expr.inₗ.injEq] at eq
    subst_vars
    exact HereditarilyNormalizing.forward_steps hnₗ mtr
  let preservesᵣ {eᵣ' : Γ ⊢ τᵣ} (eq : wn.e' = Expr.inᵣ eᵣ') : HereditarilyNormalizing eᵣ'
  := by simp_all only

  ⟨wn, preservesₗ, preservesᵣ⟩

private def inₗ_hn_inv
  {Γ : Context} {τₗ τᵣ : Ty} {eₗ : Γ ⊢ τₗ}
  (hn : HereditarilyNormalizing (@Expr.inₗ _ τₗ τᵣ eₗ)) :
  HereditarilyNormalizing eₗ := by
  let rec helper
    {Γ : Context} {τₗ τᵣ : Ty} {eₗ : Γ ⊢ τₗ} {e' : Γ ⊢ Ty.sum τₗ τᵣ} :
    (Expr.inₗ eₗ ⟶* e') →
    Σ' eₗ' : Γ ⊢ τₗ, e' = Expr.inₗ eₗ'
    | .refl _ => ⟨_, rfl⟩
    | .trans _ tr mtr =>
        match tr with
        | .ξ_inₗ tr => by
            let ⟨_, h⟩ := helper mtr
            subst h
            simp_all only [Expr.inₗ.injEq]
            exact ⟨_, rfl⟩

  let ⟨⟨mtr, norm⟩, preservesₗ, _⟩ := hn
  let ⟨_, h⟩ := helper mtr
  subst_vars
  exact HereditarilyNormalizing.backward_steps (preservesₗ rfl) (Transitionᵣₜ.ξ_inₗ_inv mtr)

private def inᵣ_hn
  {Γ : Context} {τₗ τᵣ : Ty} {eᵣ : Γ ⊢ τᵣ}
  (hnᵣ : HereditarilyNormalizing eᵣ) :
  HereditarilyNormalizing (@Expr.inᵣ _ τₗ τᵣ eᵣ) :=
  let ⟨mtr, norm⟩ := hnᵣ.weakly_normalizing
  let wn := ⟨Transitionᵣₜ.ξ_inᵣ mtr, Normal.inᵣ norm⟩
  let preservesₗ {eₗ' : Γ ⊢ τₗ} (eq : wn.e' = Expr.inₗ eₗ') : HereditarilyNormalizing eₗ'
  := by simp_all only
  let preservesᵣ {eᵣ' : Γ ⊢ τᵣ} (eq : wn.e' = Expr.inᵣ eᵣ') : HereditarilyNormalizing eᵣ'
  := by
    simp only [Expr.inᵣ.injEq] at eq
    subst_vars
    exact HereditarilyNormalizing.forward_steps hnᵣ mtr

  ⟨wn, preservesₗ, preservesᵣ⟩

private def inᵣ_hn_inv
  {Γ : Context} {τₗ τᵣ : Ty} {eᵣ : Γ ⊢ τᵣ}
  (hn : HereditarilyNormalizing (@Expr.inᵣ _ τₗ τᵣ eᵣ)) :
  HereditarilyNormalizing eᵣ := by
  let rec helper
    {Γ : Context} {τₗ τᵣ : Ty} {eᵣ : Γ ⊢ τᵣ} {e' : Γ ⊢ Ty.sum τₗ τᵣ} :
    (Expr.inᵣ eᵣ ⟶* e') →
    Σ' eᵣ' : Γ ⊢ τᵣ, e' = Expr.inᵣ eᵣ'
    | .refl _ => ⟨_, rfl⟩
    | .trans _ tr mtr =>
        match tr with
        | .ξ_inᵣ tr => by
            let ⟨_, h⟩ := helper mtr
            subst h
            simp_all only [Expr.inᵣ.injEq]
            exact ⟨_, rfl⟩

  let ⟨⟨mtr, norm⟩, _, preservesᵣ⟩ := hn
  let ⟨_, h⟩ := helper mtr
  subst_vars
  exact HereditarilyNormalizing.backward_steps (preservesᵣ rfl) (Transitionᵣₜ.ξ_inᵣ_inv mtr)

private def binary_case_hn
  {Γ : Context} {τ τₗ τᵣ : Ty}{e : Γ ⊢ Ty.sum τₗ τᵣ} {eₗ : (τₗ :: Γ) ⊢ τ} {eᵣ : (τᵣ :: Γ) ⊢ τ}
  (hn : HereditarilyNormalizing e)
  (hnₗ : {eₗ' : Γ ⊢ τₗ} → HereditarilyNormalizing eₗ' → hn.weakly_normalizing.e' = Expr.inₗ eₗ' → HereditarilyNormalizing (eₗ [ eₗ' ]))
  (hnᵣ : {eᵣ' : Γ ⊢ τᵣ} → HereditarilyNormalizing eᵣ' → hn.weakly_normalizing.e' = Expr.inᵣ eᵣ' → HereditarilyNormalizing (eᵣ [ eᵣ' ])) :
  HereditarilyNormalizing (Expr.binary_case e eₗ eᵣ) :=
  let hn@⟨⟨mtr, norm⟩, preservesₗ, preservesᵣ⟩ := hn

  match norm with
  | .neutral neut =>
      HereditarilyNormalizing.backward_steps (Neutral.binary_case neut).hereditarily_normalizing
                                             (Transitionᵣₜ.ξ_binary_case mtr)
  | .value val => by
      match val with
      | .inₗ val =>
          rename_i eₗ' _ _ _

          apply HereditarilyNormalizing.backward_steps (hnₗ (preservesₗ rfl) rfl)
          calc Expr.binary_case e eₗ eᵣ
            _ ⟶* _ := Transitionᵣₜ.ξ_binary_case mtr
            _ ⟶ _ := Transition.β_binary_caseₗ (by simp) val
      | .inᵣ val =>
          rename_i eᵣ' _ _ _

          apply HereditarilyNormalizing.backward_steps (hnᵣ (preservesᵣ rfl) rfl)
          calc Expr.binary_case e eₗ eᵣ
            _ ⟶* _ := Transitionᵣₜ.ξ_binary_case mtr
            _ ⟶ _ := Transition.β_binary_caseᵣ (by simp) val

private def abstraction_hn
  {Γ : Context} {τ₁ τ₂ : Ty} {e : (τ₁ :: Γ) ⊢ τ₂}
  (hn : {e' : Γ ⊢ τ₁} → HereditarilyNormalizing e' → HereditarilyNormalizing (e [ e' ])) :
  HereditarilyNormalizing (Expr.abstraction e) :=
  let preserves {e' : Γ ⊢ τ₁} (hn' : HereditarilyNormalizing e') : HereditarilyNormalizing (Expr.application (Expr.abstraction e) e')
  := by
    let { e' := e'', normalizes := { mtr := mtr', norm := norm'' } } := hn'.weakly_normalizing
    let hn := hn (HereditarilyNormalizing.forward_steps hn' mtr')

    apply HereditarilyNormalizing.backward_steps hn
    calc Expr.application (Expr.abstraction e) e'
      _ ⟶* Expr.application (Expr.abstraction e) e'' :=
        Transitionᵣₜ.ξ_application₂ Value.abstraction.normal mtr'
      _ ⟶ _ := Transition.β_application (by simp) norm''
  ⟨⟨Transitionᵣₜ.refl _, Value.abstraction.normal⟩, preserves⟩

private def application_hn
  {Γ : Context} {τ₁ τ₂ : Ty} {e₁ : Γ ⊢ Ty.arrow τ₁ τ₂} {e₂ : Γ ⊢ τ₁}
  (hn₁ : HereditarilyNormalizing e₁) (hn₂ : HereditarilyNormalizing e₂) :
  HereditarilyNormalizing (Expr.application e₁ e₂) :=
  let ⟨_, preserves⟩ := hn₁
  preserves hn₂

private def generic_ext_hn
  {Γ : Context} {ρ ρ' τ_in τ_out : Ty} {τ_op : TyOperator}
  (s : TyOperator.Subst ρ τ_op τ_in) (s' : TyOperator.Subst ρ' τ_op τ_out)
  (e : Γ ⊢ τ_in) (e' : ρ :: Γ ⊢ ρ') (hn : HereditarilyNormalizing e)
  (hn' : {e : Γ ⊢ ρ} → HereditarilyNormalizing e → HereditarilyNormalizing (e' [ e ])) :
  HereditarilyNormalizing (Expr.generic_ext τ_op s s' e' e) :=
  match τ_in, τ_out, τ_op, s, s' with
  | _, _, _, TyOperator.Subst.var, .var =>
      let hn' := hn' hn
      HereditarilyNormalizing.backward_step hn' (Transition.β_generic_ext_var _ _ (by simp))
  | _, _, _, .unit, .unit => HereditarilyNormalizing.backward_step hn (Transition.β_generic_ext_unit _ _)
  | _, _, .prod τ_opₗ τ_opᵣ, .prod sₗ sᵣ, .prod sₗ' sᵣ' =>
      let ⟨_, hnₗ, hnᵣ⟩ := hn
      let hnₗ := generic_ext_hn sₗ sₗ' (Expr.projₗ e) e' hnₗ hn'
      let hnᵣ := generic_ext_hn sᵣ sᵣ' (Expr.projᵣ e) e' hnᵣ hn'
      let hn := pair_hn hnₗ hnᵣ
      HereditarilyNormalizing.backward_step hn (Transition.β_generic_ext_prod _ _ _ _ _ _)
  | _, _, _, .void, .void => HereditarilyNormalizing.backward_step (nullary_case_hn hn) (Transition.β_generic_ext_void _ _)
  | _, _, .sum τ_opₗ τ_opᵣ, .sum sₗ sᵣ, .sum sₗ' sᵣ' =>
      let hn@⟨⟨mtr, norm⟩, _, _⟩ := hn

      match norm with
      | .neutral neut => by
          apply HereditarilyNormalizing.backward_steps (Neutral.binary_case neut).hereditarily_normalizing
          calc _
            _ ⟶ _ := Transition.β_generic_ext_sum _ _ _ _ _ _ rfl rfl
            _ ⟶* _ := Transitionᵣₜ.ξ_binary_case mtr
      | .value val =>
          match val with
          | .inₗ val =>
              let hn := binary_case_hn hn
                (λ hn _ => by
                  let hnₗ := generic_ext_hn sₗ sₗ' _ e' hn hn'
                  exact inₗ_hn (by simp [Expr.swap]; exact hnₗ))
                (λ _ h => by
                  subst_vars
                  simp [HereditarilyNormalizing.weakly_normalizing] at h)
              HereditarilyNormalizing.backward_step hn (Transition.β_generic_ext_sum _ _ _ _ _ _ rfl rfl)
          | .inᵣ val =>
              let hn := binary_case_hn hn
                (λ _ h => by
                  subst_vars
                  simp [HereditarilyNormalizing.weakly_normalizing] at h)
                (λ hn _ => by
                  let hnᵣ := generic_ext_hn sᵣ sᵣ' _ e' hn hn'
                  exact inᵣ_hn (by simp [Expr.swap]; exact hnᵣ))
              HereditarilyNormalizing.backward_step hn (Transition.β_generic_ext_sum _ _ _ _ _ _ rfl rfl)
  | _, _, .arrow τ₁ τ_op₂, .arrow s₂, .arrow s₂' =>
      let hn := abstraction_hn
        (λ hn'' => by
          simp [Expr.swap]
          exact generic_ext_hn s₂ s₂' _ e' (application_hn hn hn'') hn')

      HereditarilyNormalizing.backward_step hn (Transition.β_generic_ext_arrow _ _ _ _ rfl rfl)

-- Main theorem
private def hereditarily_normalizing
  {Γ Δ : Context} {τ : Ty} {σ : Subst Γ Δ}
  (e : Γ ⊢ τ)
  (hn_σ : HereditarilyNormalizingSubst σ) :
  HereditarilyNormalizing ((⟪ σ ⟫) e) :=
  match e with
  | .var a => hn_σ a
  | .triv => ⟨Transitionᵣₜ.refl _, Value.triv.normal⟩
  | .pair eₗ eᵣ => pair_hn (hereditarily_normalizing eₗ hn_σ) (hereditarily_normalizing eᵣ hn_σ)
  | .projₗ e => (hereditarily_normalizing e hn_σ).2.1
  | .projᵣ e => (hereditarily_normalizing e hn_σ).2.2
  | .nullary_case e => nullary_case_hn (hereditarily_normalizing e hn_σ)
  | .inₗ eₗ => inₗ_hn (hereditarily_normalizing eₗ hn_σ)
  | .inᵣ eᵣ => inᵣ_hn (hereditarily_normalizing eᵣ hn_σ)
  | @Expr.binary_case _ _ τₗ τᵣ e eₗ eᵣ =>
      let hn := hereditarily_normalizing e hn_σ
      let hnₗ {eₗ' : Δ ⊢ τₗ} (hnₗ' : HereditarilyNormalizing eₗ') (_ : hn.weakly_normalizing.e' = Expr.inₗ eₗ') : HereditarilyNormalizing (((⟪ σ.exts ⟫) eₗ) [ eₗ' ])
      := by
        let σ' : Subst (τₗ :: Γ) Δ := Subst.cons eₗ' σ
        let hn_σ' : HereditarilyNormalizingSubst σ'
        | _, .here => hnₗ'
        | _, .there a => hn_σ a
        simp
        exact hereditarily_normalizing eₗ hn_σ'
      let hnᵣ {eᵣ' : Δ ⊢ τᵣ} (hnᵣ' : HereditarilyNormalizing eᵣ') (_ : hn.weakly_normalizing.e' = Expr.inᵣ eᵣ') : HereditarilyNormalizing (((⟪ σ.exts ⟫) eᵣ) [ eᵣ' ])
      := by
        let σ' : Subst (τᵣ :: Γ) Δ := Subst.cons eᵣ' σ
        let hn_σ' : HereditarilyNormalizingSubst σ'
        | _, .here => hnᵣ'
        | _, .there a => hn_σ a
        simp
        exact hereditarily_normalizing eᵣ hn_σ'

      binary_case_hn hn hnₗ hnᵣ
  | @Expr.generic_ext .(Γ) ρ ρ' τ_in τ_out τ_op s s' e' e =>
      let hn := hereditarily_normalizing e hn_σ
      let hn' {e : Δ ⊢ ρ} (hn : HereditarilyNormalizing e) : HereditarilyNormalizing (((⟪ σ.exts ⟫) e') [ e ]) := by
        let σ' : Subst (ρ :: Γ) Δ := e •` σ
        let hn_σ' : HereditarilyNormalizingSubst σ'
        | _, .here => hn
        | _, .there a => hn_σ a
        let hn' := hereditarily_normalizing e' hn_σ'
        simp
        exact hn'

      generic_ext_hn s s' ((⟪ σ ⟫) e) _ hn hn'
  | @Expr.abstraction _ τ₁ _ e =>
      let hn {e' : Δ ⊢ τ₁} (hn' : HereditarilyNormalizing e') : HereditarilyNormalizing (((⟪ σ.exts ⟫) e) [ e' ]) := by
        let σ' : Subst (τ₁ :: Γ) Δ := e' •` σ
        let hn_σ' : HereditarilyNormalizingSubst σ'
        | _, .here => hn'
        | _, .there a => hn_σ a
        simp
        exact hereditarily_normalizing e hn_σ'
      abstraction_hn hn
  | .application e₁ e₂ => application_hn (hereditarily_normalizing e₁ hn_σ) (hereditarily_normalizing e₂ hn_σ)

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
