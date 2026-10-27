import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Fourier.FastFourierTransform.Part2
open Fourier.FastFourierTransformWanted


/--
[fftCost_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/FastFourierTransform.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (hn : 0 < n) :
-- imply
  fftCost (2 * n) = 2 * fftCost n + 2 * n := by
-- proof
  unfold fftCost
  have hlog : Nat.log 2 (2 * n) = Nat.log 2 n + 1 := by
    simpa only [Nat.mul_comm] using
      Nat.log_mul_base (b := 2) (n := n) (by decide) (Nat.ne_of_gt hn)
  rw [hlog, mul_add, mul_one, mul_assoc]


-- created on 2026-10-24
