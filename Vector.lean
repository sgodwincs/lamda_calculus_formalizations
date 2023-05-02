universe u

inductive Vector (α : Type u) : Nat → Type u where
  | nil : Vector α 0
  | cons {n : Nat} : α → Vector α n → Vector α (Nat.succ n)

infixr:67 " :: " => Vector.cons

namespace Vector

def cast {α : Type u} {m n : Nat} (v : Vector α m) (h : m = n) : Vector α n := h ▸ v

@[simp]
theorem cast_rfl {α : Type u} {n : Nat} (v : Vector α n) : v.cast rfl = v := rfl

@[simp]
theorem cast_cast {α : Type u} {n n' n'' : Nat} (v : Vector α n) (h : n = n') (h' : n' = n'') :
    (v.cast h).cast h' = v.cast (h.trans h') := by subst_vars; rfl

@[simp]
theorem cast_cons
  {α : Type u} {n n' : Nat}
  (v : Vector α n) (a : α) (h : n.succ = n'.succ) :
  (a :: v).cast h = a :: (v.cast (by simp_all only [Nat.succ.injEq])) :=
by
  cases h
  simp only [cast_rfl]

def append {α : Type u} {m n : Nat} : Vector α m → Vector α n → Vector α (m + n)
  | nil, ys => ys.cast (by simp [Nat.succ_add])
  | x :: xs, ys => (cons x (append xs ys)).cast (by simp only [Nat.succ_add])

@[simp]
theorem nil_append {n : Nat} {α : Type} (as : Vector α n) : append nil as = as.cast (Nat.zero_add n).symm := rfl

@[simp]
theorem cons_append {α : Type u} {m n : Nat} (a : α) (as : Vector α m) (bs : Vector α n) : append (a :: as) bs = (a :: (append as bs)).cast (Nat.succ_add m n).symm := rfl
