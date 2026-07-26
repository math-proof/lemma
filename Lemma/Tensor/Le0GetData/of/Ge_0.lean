import sympy.series.limits
import sympy.tensor.tensor
import Lemma.Vector.EqGet0_0
open Vector


@[main]
private lemma main
  {A : Tensor ℝ* s}
-- given
  (h_pos : A ≥ 0)
  (k : Fin s.prod) :
-- imply
  A.data[k] ≥ 0 := by
-- proof
  have h' := h_pos k
  simp only [LE.le] at h'
  rw [show ((0 : Tensor ℝ* s).data)[k] = 0 from EqGet0_0.fin (α := ℝ*) k] at h'
  exact ge_iff_le.mp h'


-- created on 2026-07-27
