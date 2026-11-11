import Lemma.Tensor.Dot.eq.Eye.of.Dot.eq.Eye
import Notation.Data.Tensor.Permute
import Lemma.Tensor.DotTInterleave.eq.Eye
import Def.Data.Tensor.Eye
import Theorem.Data.Tensor.Functions
import Instance.Data.Vector.Basic.Dot
open Tensor


@[path]
private lemma main :
-- imply
  (interleave d) ⬝ᵥ (interleave d)ᵀ = Tensor.eye (d + d) := by
-- proof
  apply Dot.eq.Eye.of.Dot.eq.Eye (A := id (α := Tensor ℝ [d + d, d + d]) (interleave d)ᵀ) (B := interleave d)
  apply DotTInterleave.eq.Eye


-- created on 2026-09-05
-- updated on 2026-10-26
