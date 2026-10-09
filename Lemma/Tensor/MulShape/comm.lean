import sympy.core.mul
import sympy.Basic
import Lemma.List.ZipWithLcm.comm.of.EqLengthS
open List Tensor


@[path]
private lemma main
-- given
  (s s' : List ℕ) :
-- imply
  mul_shape s s' = mul_shape s' s := by
-- proof
  have hmax : s.length ⊔ s'.length = s'.length ⊔ s.length := max_comm _ _
  simp only [mul_shape, hmax]
  exact ZipWithLcm.comm.of.EqLengthS _ _ (by
    rw [← hmax]
    exact pad1_length_eq s s')


-- created on 2026-10-07
