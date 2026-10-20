import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Bernoulli.GesselIdentity
open MetaMathlibExt


/--
[gessel_bernoulli_number_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/GesselIdentity.lean)
-/
@[path]
private lemma gessel_bernoulli_number_identity_eq
  {n r m : ℕ}
-- given
  (hr : Odd r)
  (hm : 1 ≤ m) :
-- imply
  Finset.sum (Finset.range (n + r + 1)) (fun k =>
    (m : ℚ) ^ (n + r - k) * (Nat.choose (n + r) k : ℚ) *
    (Nat.choose (n + k + r) r : ℚ) * bernoulli (n + k)) =
    (((r : ℚ) + 1) / 2) * Finset.sum (Finset.Ico 1 m) (fun k =>
    Finset.sum (Finset.range (r + 2)) (fun j =>
    (Nat.choose (n + r) j : ℚ) * (Nat.choose (n + r) (r + 1 - j) : ℚ) *
    (k : ℚ) ^ ((j : ℤ) + (n : ℤ) - 1) *
    (((k : ℚ) - (m : ℚ)) ^ ((n : ℤ) + (r : ℤ) - (j : ℤ))))) := by
-- proof
  apply MetaMathlibExt.gessel_bernoulli_number_identity n r m hr hm


-- created on 2026-10-20
