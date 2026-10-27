import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Fourier.FastFourierTransform.Part2
open Fourier.FastFourierTransformWanted


/--
[dftSum_mod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/FastFourierTransform.lean)
-/
@[path]
private lemma dft_sum_mod_eq
-- given
  (n : ℕ)
  (ω : ℂ)
  (hω : ω ^ n = 1)
  (f : ℕ → ℂ)
  (K : ℕ) :
-- imply
  dftSum n ω f K = dftSum n ω f (K % n) := by
-- proof
  apply dftSum_mod n ω hω f K


-- created on 2026-10-10
-- updated on 2026-10-26
