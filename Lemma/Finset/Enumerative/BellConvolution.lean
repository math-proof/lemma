import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.BellConvolution
open MetaMathlibExt


/--
[bell_eq_signed_stirlingFirst_convolution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BellConvolution.lean)
-/
@[path]
private lemma bell_eq_signed_stirlingFirst_convolution_eq
  {n p : ℕ} :
-- imply
  (Nat.bell n : ℤ) =
    ∑ k ∈ Finset.range (n + 1),
    (-(p : ℤ)) ^ (n - k) * (Nat.choose n k : ℤ) *
    (∑ m ∈ Finset.range (p + 1),
    (Nat.bell (k + m) : ℤ) * ((-1 : ℤ) ^ (p - m) * (Nat.stirlingFirst p m : ℤ))) := by
-- proof
  apply MetaMathlibExt.bell_eq_signed_stirlingFirst_convolution n p


-- created on 2026-10-20
