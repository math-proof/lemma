import stdlib.SEq
import sympy.Basic
import sympy.tensor.tensor


@[main]
private lemma main
  [Zero α]
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
  X.resize d n ≃ X'.resize d' n' := by
-- proof
  subst h_n
  have h_s := h.left
  subst h_s
  simp [SEq] at *
  grind


-- created on 2026-07-10
