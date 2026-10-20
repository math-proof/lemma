import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MedianEulerNumber
open scoped BigOperators
open MetaMathlibExt


/--
[medianEulerNumber_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MedianEulerNumber.lean)
-/
@[path]
private lemma medianEulerNumber_zero_eq
  :
-- imply
  medianEulerNumber 0 = 1 := by
-- proof
  apply MetaMathlibExt.medianEulerNumber_zero

/--
[medianEulerNumber_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MedianEulerNumber.lean)
-/
@[path]
private lemma medianEulerNumber_one_eq
  :
-- imply
  medianEulerNumber 1 = 3 := by
-- proof
  apply MetaMathlibExt.medianEulerNumber_one

/--
[medianEulerNumber_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MedianEulerNumber.lean)
-/
@[path]
private lemma medianEulerNumber_two_eq
  :
-- imply
  medianEulerNumber 2 = 24 := by
-- proof
  apply MetaMathlibExt.medianEulerNumber_two

/--
[medianEulerNumber_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MedianEulerNumber.lean)
-/
@[path]
private lemma medianEulerNumber_three_eq
  :
-- imply
  medianEulerNumber 3 = 402 := by
-- proof
  apply MetaMathlibExt.medianEulerNumber_three

/--
[medianEulerCoeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MedianEulerNumber.lean)
-/
@[path]
private lemma medianEulerCoeff_zero_eq
  :
-- imply
  medianEulerCoeff 0 = 1 := by
-- proof
  apply MetaMathlibExt.medianEulerCoeff_zero

/--
[medianEulerCoeff_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MedianEulerNumber.lean)
-/
@[path]
private lemma medianEulerCoeff_succ_eq
  {n : ℕ} :
-- imply
  medianEulerCoeff (n + 1)
    = (if (n + 1) % 2 = 1 then 1 else 0) -
    ∑ j ∈ Finset.filter (fun j => 2 ≤ j ∧ j % 2 = 0) (Finset.range (n + 1 + 1)),
    ((n + 1).choose j : ℤ) * medianEulerCoeff (n + 1 - j) := by
-- proof
  apply MetaMathlibExt.medianEulerCoeff_succ n

/--
[medianEulerCoeff_egf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MedianEulerNumber.lean)
-/
@[path]
private lemma medianEulerCoeff_egf_eq
  :
-- imply
  (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) *
    PowerSeries.mk (fun n => ((medianEulerCoeff n : ℤ) : ℚ) / (n.factorial : ℚ))
    = 2 + PowerSeries.exp ℚ - PowerSeries.rescale (-1) (PowerSeries.exp ℚ) := by
-- proof
  apply MetaMathlibExt.medianEulerCoeff_egf

/--
[medianEulerNumber_div_three_and_modFive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MedianEulerNumber.lean)
-/
@[path]
private lemma medianEulerNumber_div_three_and_modFive_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  3 ∣ medianEulerNumber n ∧ Nat.ModEq 5 (medianEulerNumber n / 3) (3 ^ (n - 1)) := by
-- proof
  apply MetaMathlibExt.medianEulerNumber_div_three_and_modFive hn


-- created on 2026-10-20
