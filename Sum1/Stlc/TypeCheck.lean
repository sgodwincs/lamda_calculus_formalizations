import Stlc.Bound
import Stlc.Statics

namespace Statics.Expr

def erase {Γ : Context} {τ : Ty} : (Γ ⊢ τ) → Bound.Expr Γ.length
  | .var a => Bound.Expr.var a.to_fin
  | @Expr.nullary_case _ τ e => Bound.Expr.nullary_case τ e.erase
  | @Expr.inl _ τₗ τᵣ e => Bound.Expr.inl τₗ τᵣ e.erase
  | @Expr.inr _ τₗ τᵣ e => Bound.Expr.inr τₗ τᵣ e.erase
  | .binary_case e eₗ eᵣ => Bound.Expr.binary_case e.erase eₗ.erase eᵣ.erase
  | @Expr.abstraction _ τ _ e => Bound.Expr.abstraction τ e.erase
  | .application e₁ e₂ => Bound.Expr.application e₁.erase e₂.erase

mutual

def infer (Γ : Context) : (e : Bound.Expr Γ.length) → Option (Σ τ : Ty, Γ ⊢ τ)
  | .var i =>
      let ⟨a⟩ := VarIn.from_fin Γ i
      some ⟨_, Expr.var a⟩
  | .nullary_case τ e => do
      let e' ← check Γ e Ty.void
      some ⟨_, @Expr.nullary_case _ τ e'⟩
  | .inl τₗ τᵣ e => do
      let e' ← check Γ e τₗ
      some ⟨_, @Expr.inl _ τₗ τᵣ e'⟩
  | .inr τₗ τᵣ e => do
      let e' ← check Γ e τᵣ
      some ⟨_, @Expr.inr _ τₗ τᵣ e'⟩
  | .binary_case e eₗ eᵣ => do
      let ⟨τ, e'⟩ ← infer Γ e

      match τ with
      | .void | .arrow _ _ => none
      | .sum τₗ τᵣ =>
          let ⟨τₗ', eₗ'⟩ ← infer (τₗ :: Γ) eₗ
          let ⟨τᵣ', eᵣ'⟩ ← infer (τᵣ :: Γ) eᵣ

          match decEq τₗ' τᵣ' with
          | isTrue _ => by subst_vars; exact some ⟨_, Expr.binary_case e' eₗ' eᵣ'⟩
          | isFalse _ => none
  | .abstraction τ e => do
      let ⟨τ', e'⟩ ← infer (τ :: Γ) e
      some ⟨_, Expr.abstraction e'⟩
  | .application e₁ e₂ => do
      let ⟨τ, e₁'⟩ ← infer Γ e₁

      match τ with
      | .void | .sum _ _ => none
      | .arrow τ τ' =>
          let e₂' ← check Γ e₂ τ
          some ⟨_, Expr.application e₁' e₂'⟩

def check (Γ : Context) : (e : Bound.Expr Γ.length) → (τ : Ty) → Option (Γ ⊢ τ)
  | .var i, τ =>
      let { τ := τ', a } := VarIn.from_fin Γ i
      match decEq τ τ' with
      | isTrue eq => some (by subst_vars; exact Expr.var a)
      | isFalse _ => none
  | @Bound.Expr.nullary_case _ τ e, τ' => do
      let e' ← check Γ e Ty.void
      match decEq τ τ' with
      | isTrue _ => some (Expr.nullary_case e')
      | isFalse _ => none
  | @Bound.Expr.inl _ τₗ τᵣ e, Ty.sum τₗ' τᵣ' => do
      let e' ← check Γ e τₗ
      match decEq τₗ τₗ', decEq τᵣ τᵣ' with
      | isTrue _, isTrue _ => by subst_vars; exact some (@Expr.inl _ τₗ' τᵣ' e')
      | _, _ => none
  | .inl _ _ _, Ty.arrow _ _  => none
  | .inl _ _ _, Ty.void  => none
  | @Bound.Expr.inr _ τₗ τᵣ e, Ty.sum τₗ' τᵣ' => do
      let e' ← check Γ e τᵣ
      match decEq τₗ τₗ', decEq τᵣ τᵣ' with
      | isTrue _, isTrue _ => by subst_vars; exact some (@Expr.inr _ τₗ' τᵣ' e')
      | _, _ => none
  | .inr _ _ _, Ty.arrow _ _  => none
  | .inr _ _ _, Ty.void  => none
  | .binary_case e eₗ eᵣ, τ' => do
      let ⟨τ, e'⟩ ← infer Γ e

      match τ with
      | .void | .arrow _ _ => none
      | .sum τₗ τᵣ =>
          let ⟨τₗ', eₗ'⟩ ← infer (τₗ :: Γ) eₗ
          let ⟨τᵣ', eᵣ'⟩ ← infer (τᵣ :: Γ) eᵣ

          match decEq τₗ' τᵣ', decEq τᵣ' τ' with
          | isTrue _, isTrue _  => by subst_vars; exact some (Expr.binary_case e' eₗ' eᵣ')
          | _, _ => none
  | .abstraction τ₁ e, Ty.arrow τ₁' τ₂ =>
      match decEq τ₁ τ₁' with
      | isTrue eq => do
          let e' ← check (τ₁' :: Γ) e τ₂
          some (by subst_vars; exact Expr.abstraction e')
      | isFalse _ => none
  | .abstraction _ _, Ty.sum _ _ => none
  | .abstraction _ _, Ty.void => none
  | .application e₁ e₂, τ' => do
      let ⟨τ, e₂'⟩ ← infer Γ e₂
      let e₁' ← check Γ e₁ (Ty.arrow τ τ')
      some (Expr.application e₁' e₂')

end

mutual

def infer_sound {Γ : Context} {τ : Ty} : (e : Γ ⊢ τ) → infer Γ e.erase = some ⟨τ, e⟩
  | .var a => by simp only [erase, infer]; rw [VarIn.to_from_fin_inverse]
  | .nullary_case e => by simp only [erase, infer, check_sound e, Bind.bind, Option.bind]
  | .inl e => by simp only [erase, infer, check_sound e, Bind.bind, Option.bind]
  | .inr e => by simp only [erase, infer, check_sound e, Bind.bind, Option.bind]
  | .binary_case e eₗ eᵣ => by simp only [infer_sound e, infer_sound eₗ, infer_sound eᵣ, erase, infer, Bind.bind, Option.bind]; aesop
  | .abstraction e => by simp only [erase, infer, infer_sound e, Bind.bind, Option.bind]
  | .application e₁ e₂ => by simp only [erase, infer, infer_sound e₁, check_sound e₂, Bind.bind, Option.bind]

def check_sound {Γ : Context} {τ : Ty} : (t : Γ ⊢ τ) → check Γ t.erase τ = some t
  | .var a => by
      simp only [erase, check]
      rw [VarIn.to_from_fin_inverse]
      cases decEq τ τ with
      | isTrue => rfl
      | isFalse => contradiction
  | .nullary_case e => by simp only [erase, check, check_sound e, Bind.bind, Option.bind]; aesop
  | @Expr.inl _ τₗ τᵣ e => by
      simp only [erase, check, check_sound e, Bind.bind, Option.bind]
      match decEq τₗ τₗ, decEq τᵣ τᵣ with
      | isTrue _, isTrue _  => rfl
      | isFalse _, _ => contradiction
  | @Expr.inr _ τₗ τᵣ e => by
      simp only [erase, check, check_sound e, Bind.bind, Option.bind]
      match decEq τₗ τₗ, decEq τᵣ τᵣ with
      | isTrue _, isTrue _  => rfl
      | isFalse _, _ => contradiction
  | .binary_case e eₗ eᵣ => by
      simp only [erase, check, infer_sound e, infer_sound eₗ, infer_sound eᵣ, Bind.bind, Option.bind]
      match decEq τ τ with
      | isTrue _ => rfl
      | isFalse _ => contradiction
  | @Expr.abstraction _ τ τ' e => by
      simp only [erase, check]
      match decEq τ τ with
      | isTrue _ => simp only [check_sound e, Bind.bind, Option.bind]
      | isFalse _ => contradiction
  | .application e₁ e₂ => by simp only [erase, check, infer_sound e₂, check_sound e₁, Bind.bind, Option.bind]

end

mutual

def infer_complete
  {Γ : Context} {e : Bound.Expr Γ.length} {τ : Ty}
  (h : infer Γ e = none) :
  (Σ' e' : Γ ⊢ τ, e'.erase = e) → Empty :=
by
  intro ⟨e, eq⟩
  match e with
  | .var a => unfold erase infer at *; subst_vars; contradiction
  | .nullary_case e =>
      unfold erase infer at *
      subst_vars
      simp only [check_sound e, Bind.bind, Option.bind] at h
  | .inl e =>
      unfold erase infer at *
      subst_vars
      simp only [check_sound e, Bind.bind, Option.bind] at h
  | .inr e =>
      unfold erase infer at *
      subst_vars
      simp only [check_sound e, Bind.bind, Option.bind] at h
  | .binary_case e eₗ eᵣ =>
      unfold erase infer at *
      subst_vars
      simp only [infer_sound e, infer_sound eₗ, infer_sound eᵣ, Bind.bind, Option.bind] at h
      match g : decEq τ τ with
      | isTrue _ => rw [g] at h; simp_all
      | isFalse _ => contradiction
  | .abstraction e =>
      unfold erase infer at *
      subst_vars
      simp only [infer_sound e, Bind.bind, Option.bind] at h
  | .application e₁ e₂ =>
      unfold erase infer at *
      subst_vars
      simp only [infer_sound e₁, check_sound e₂, Bind.bind, Option.bind] at h

def check_complete
  {Γ : Context} {e : Bound.Expr Γ.length} {τ : Ty}
  (h : check Γ e τ = none) :
  (Σ' e' : Γ ⊢ τ, e'.erase = e) → Empty :=
by
  intro ⟨e, eq⟩
  match e with
  | .var a =>
      unfold erase check at *
      subst eq
      simp at h
      rw [VarIn.to_from_fin_inverse] at h
      match h' : decEq τ τ with
      | isTrue _ => subst_vars; simp_all only
      | isFalse _ => contradiction
  | .nullary_case e =>
      unfold erase check at *
      subst_vars
      simp only [check_sound e, Bind.bind, Option.bind] at h
      match g : decEq τ τ with
      | isTrue _ => rw [g] at h; simp_all
      | isFalse _ => contradiction
  | @Expr.inl _ τₗ τᵣ e =>
      unfold erase check at *
      subst_vars
      simp only [check_sound e, Bind.bind, Option.bind] at h
      match gₗ : decEq τₗ τₗ, gᵣ : decEq τᵣ τᵣ with
      | isTrue _, isTrue _ => rw [gₗ, gᵣ] at h; simp_all
      | isFalse _, _ => contradiction
  | @Expr.inr _ τₗ τᵣ e =>
      unfold erase check at *
      subst_vars
      simp only [check_sound e, Bind.bind, Option.bind] at h
      match gₗ : decEq τₗ τₗ, gᵣ : decEq τᵣ τᵣ with
      | isTrue _, isTrue _ => rw [gₗ, gᵣ] at h; simp_all
      | isFalse _, _ => contradiction
  | .binary_case e eₗ eᵣ =>
      unfold erase check at *
      subst_vars
      simp only [infer_sound e, infer_sound eₗ, infer_sound eᵣ, Bind.bind, Option.bind] at h
      match g : decEq τ τ with
      | isTrue _ => rw [g] at h; simp_all
      | isFalse _ => contradiction
  | @Expr.abstraction _ τ _ e =>
      unfold erase check at *
      subst_vars
      simp only at h
      match h' : decEq τ τ with
      | isTrue _ => subst_vars; simp_all only [check_sound e, Bind.bind, Option.bind]
      | isFalse _ => contradiction
  | .application e₁ e₂ =>
      unfold erase check at *
      subst_vars
      simp only [check_sound e₁, infer_sound e₂, Bind.bind, Option.bind] at h

end
