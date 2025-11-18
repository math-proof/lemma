import sympy.tensor.Basic
import stdlib.SEq


@[main]
private lemma main
  {X : Tensor α s}
  {X' : Tensor α s'}
  {n n' : ℕ}
  {d : Fin s.length}
  {d' : Fin s'.length}
-- given
  (h_n : n = n')
  (h_d : d.val = d'.val)
  (h : X ≃ X') :
-- imply
  X.repeat n d ≃ X'.repeat n' d' := by
-- proof
  subst h_n
  have h_s := h.left
  subst h_s
  simp [SEq] at *
  grind



-- created on 2025-10-11
