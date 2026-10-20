import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.DigitalBinomialTheorem
open scoped BigOperators
open MetaMathlibExt


/--
[binDigitSum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/DigitalBinomialTheorem.lean)
-/
@[path]
private lemma binDigitSum_zero_eq
  :
-- imply
  binDigitSum 0 = 0 := by
-- proof
  apply MetaMathlibExt.binDigitSum_zero

/--
[binDigitSum_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/DigitalBinomialTheorem.lean)
-/
@[path]
private lemma binDigitSum_two_mul_eq
  {k : ℕ} :
-- imply
  binDigitSum (2 * k) = binDigitSum k := by
-- proof
  apply MetaMathlibExt.binDigitSum_two_mul k

/--
[binDigitSum_two_mul_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/DigitalBinomialTheorem.lean)
-/
@[path]
private lemma binDigitSum_two_mul_add_one_eq
  {k : ℕ} :
-- imply
  binDigitSum (2 * k + 1) = binDigitSum k + 1 := by
-- proof
  apply MetaMathlibExt.binDigitSum_two_mul_add_one k

/--
[binDigitSum_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/DigitalBinomialTheorem.lean)
-/
@[path]
private lemma binDigitSum_one_eq
  :
-- imply
  binDigitSum 1 = 1 := by
-- proof
  apply MetaMathlibExt.binDigitSum_one

/--
[digital_binomial_theorem_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/DigitalBinomialTheorem.lean)
-/
@[path]
private lemma digital_binomial_theorem_general_eq
  [CommSemiring R]
  {n : ℕ}
  {x y : R} :
-- imply
  (x + y) ^ binDigitSum n =
    ∑ m ∈ Finset.filter
    (fun m => binDigitSum m + binDigitSum (n - m) = binDigitSum n)
    (Finset.range (n + 1)),
    x ^ binDigitSum m * y ^ binDigitSum (n - m) := by
-- proof
  apply MetaMathlibExt.digital_binomial_theorem_general n x y

/--
[digital_binomial_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/DigitalBinomialTheorem.lean)
-/
@[path]
private lemma digital_binomial_theorem_eq
  [CommRing R]
  {n : ℕ}
  {x y : R} :
-- imply
  (x + y) ^ binDigitSum n =
    ∑ m ∈ Finset.filter
    (fun m => binDigitSum m + binDigitSum (n - m) = binDigitSum n)
    (Finset.range (n + 1)),
    x ^ binDigitSum m * y ^ binDigitSum (n - m) := by
-- proof
  apply MetaMathlibExt.digital_binomial_theorem n x y


-- created on 2026-10-20
