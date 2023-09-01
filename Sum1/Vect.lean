universe u

inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons {n : Nat} : α → Vect α n → Vect α n.succ

notation "[]ᵥ" => Vect.nil
infixr:67 " ::ᵥ " => Vect.cons

namespace Vect

abbrev cast {α : Type u} {m n : Nat} (v : Vect α m) (h : m = n) : Vect α n := h ▸ v

@[simp]
theorem cast_rfl {α : Type u} {n : Nat} (v : Vect α n) : v.cast rfl = v := rfl

@[simp]
theorem cast_cast
  {α : Type u} {n n' n'' : Nat}
  (v : Vect α n) (h : n = n') (h' : n' = n'') :
    (v.cast h).cast h' = v.cast (h.trans h')
:= by
  subst_vars
  rfl

@[simp]
theorem cast_cons
  {α : Type u} {n n' : Nat}
  (v : Vect α n) (a : α) (h : n.succ = n'.succ) :
  (a ::ᵥ v).cast h = a ::ᵥ (v.cast (by simp_all only [Nat.succ.injEq]))
:= by
  cases h
  simp only [cast_rfl]

def append {α : Type u} {m n : Nat} : Vect α m → Vect α n → Vect α (m + n)
  | []ᵥ, ys => ys.cast (by simp [Nat.succ_add])
  | x ::ᵥ xs, ys => (x ::ᵥ (append xs ys)).cast (by simp only [Nat.succ_add])

@[simp]
theorem nil_append {n : Nat} {α : Type} (as : Vect α n) : append []ᵥ as = as.cast (Nat.zero_add n).symm := rfl

@[simp]
theorem cons_append
  {α : Type u} {m n : Nat}
  (a : α) (as : Vect α m) (bs : Vect α n) :
  append (a ::ᵥ as) bs = (a ::ᵥ (append as bs)).cast (Nat.succ_add m n).symm
:=
  rfl
