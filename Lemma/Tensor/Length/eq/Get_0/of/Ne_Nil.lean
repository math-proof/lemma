import sympy.tensor.Basic
import Lemma.List.Ne_Nil.is.GtLength_0
open List


@[main, comm]
private lemma main
-- given
  (h : s ≠ [])
  (X : Tensor α s) :
-- imply
  X.length = s.get ⟨0, GtLength_0.of.Ne_Nil h⟩ := by
-- proof
  simp [Tensor.length]
  cases s
  ·
    contradiction
  ·
    cases X
    simp


-- created on 2025-10-10
