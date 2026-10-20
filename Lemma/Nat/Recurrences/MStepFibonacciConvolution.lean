import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.MStepFibonacciConvolution
open MetaMathlibExt


/--
[two_pow_convolution_mstep_fibonacci](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/MStepFibonacciConvolution.lean)
-/
@[path]
private lemma two_pow_convolution_mstep_fibonacci_eq
  {F : ℕ → ℕ}
  {m n : ℕ}
-- given
  (hm : 1 ≤ m)
  (h0 : F 0 = 0)
  (h1 : F 1 = 1)
  (hrec : ∀ k : ℕ, 2 ≤ k → F k = ∑ j ∈ Finset.range m, F (k - (j + 1))) :
-- imply
  (∑ j ∈ Finset.range (n + 1), 2 ^ j * F (n - j)) =
    2 ^ (n + m - 1) - F (n + 1 + m) := by
-- proof
  apply MetaMathlibExt.two_pow_convolution_mstep_fibonacci F m n hm h0 h1 hrec


-- created on 2026-10-20
