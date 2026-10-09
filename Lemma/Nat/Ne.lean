import sympy.sets.sets
import sympy.Basic


@[path]
private lemma reverse
  {a b : α}
-- given
  (h : a ≠ b) :
-- imply
  b ≠ a := by
-- proof
  exact h.symm


@[path]
private lemma simp.common_terms
  [AddGroup α]
  {x y a : α}
-- given
  (h : x + a ≠ y + a) :
-- imply
  x ≠ y := by
-- proof
  exact fun e => h (by rw [e])


@[path]
private lemma transport
  [AddGroup α]
  {x y a : α}
-- given
  (h : x + a ≠ y) :
-- imply
  x ≠ y - a := by
-- proof
  exact fun e => h (by rw [e, sub_add_cancel])


-- created on 2020-02-07
