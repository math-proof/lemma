import sympy.core.mul
import sympy.Basic
import Lemma.Tensor.MulShape.comm
import Lemma.Tensor.WrapFlatPad1LeftWrapFlat.eq.WrapFlatPad1.of.NeProdMulShapeMulShape_0.NeProdMulShape_0
open Tensor


/--
Wrapping `B` through `B.mul C`, then through `A.mul (B.mul C)`.
-/
@[main]
private lemma main
-- given
  (s s' s'' : List ℕ)
  (i : ℕ)
  (hBC : (mul_shape s' s'').prod ≠ 0)
  (hout : (mul_shape s (mul_shape s' s'')).prod ≠ 0) :
-- imply
  wrapFlat (pad1 s' (s'.length ⊔ s''.length)) (mul_shape s' s'')
      (wrapFlat
        (pad1 (mul_shape s' s'')
          (s.length ⊔ (mul_shape s' s'').length))
        (mul_shape s (mul_shape s' s'')) i) =
      wrapFlat (pad1 s' (s.length ⊔ s'.length ⊔ s''.length))
        (mul_shape s (mul_shape s' s'')) i := by
-- proof
  have h := WrapFlatPad1LeftWrapFlat.eq.WrapFlatPad1.of.NeProdMulShapeMulShape_0.NeProdMulShape_0 s' s'' s i hBC (by
    rwa [MulShape.comm])
  simp only [MulShape.comm (mul_shape s' s'') s,
    max_comm (mul_shape s' s'').length s.length,
    max_comm (s'.length ⊔ s''.length) s.length] at h
  rw [max_assoc]
  exact h


-- created on 2026-10-07
