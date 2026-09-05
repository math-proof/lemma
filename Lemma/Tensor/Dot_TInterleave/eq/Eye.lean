import Lemma.Tensor.Dot.eq.Eye.of.Dot.eq.Eye
import Lemma.Tensor.DotTInterleave.eq.Eye
import Lemma.Tensor.Interleave.eq.AppendStackS_Delta
import sympy.matrices.expressions.special
import sympy.tensor.functions
open Tensor


@[main]
private lemma main :
-- imply
  (interleave d) @ (interleave d)ᵀ = Tensor.eye (d + d) := by
-- proof
  apply Dot.eq.Eye.of.Dot.eq.Eye (A := id (α := Tensor ℝ [d + d, d + d]) (interleave d)ᵀ) (B := interleave d)
  apply DotTInterleave.eq.Eye


-- created on 2026-09-05
-- updated on 2026-09-06
