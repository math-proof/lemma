import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Fourier.FastFourierTransform.Part2
open Fourier.FastFourierTransformWanted


/--
[cooley_tukey](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/FastFourierTransform.lean)
-/
@[path]
private lemma cooley_tukey_eq
-- given
  (n : ℕ)
  (ω : ℂ)
  (hω : ω ^ (2 * n) = 1)
  (f : ℕ → ℂ)
  (K : ℕ) :
-- imply
  dftSum (2 * n) ω f K =
    dftSum n (ω ^ 2) (fun t => f (2 * t)) (K % n) +
      ω ^ K * dftSum n (ω ^ 2) (fun t => f (2 * t + 1)) (K % n) := by
-- proof
  apply cooley_tukey n ω hω f K


-- created on 2026-10-10
-- updated on 2026-10-26
