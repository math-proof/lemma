import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SimsekNumber
open MetaMathlibExt


/--
[simsekNumber_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SimsekNumber.lean)
-/
@[path]
private lemma simsekNumber_eq_sum_eq
  {n k : Nat}
  {lam : ℂ} :
-- imply
  simsekNumber n k lam =
      ((k.factorial : ℂ))⁻¹ *
        ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * (((j : ℂ) ^ n) * (lam ^ j)) := by
-- proof
  apply MetaMathlibExt.simsekNumber_eq_sum n k lam

/--
[simsekNumber_zero_k](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SimsekNumber.lean)
-/
@[path]
private lemma simsekNumber_zero_k_eq
  {n : Nat}
  {lam : ℂ} :
-- imply
  simsekNumber n 0 lam = (0 : ℂ) ^ n := by
-- proof
  apply MetaMathlibExt.simsekNumber_zero_k n lam

/--
[simsekNumber_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SimsekNumber.lean)
-/
@[path]
private lemma simsekNumber_zero_zero_eq
  {lam : ℂ} :
-- imply
  simsekNumber 0 0 lam = 1 := by
-- proof
  apply MetaMathlibExt.simsekNumber_zero_zero lam


-- created on 2026-10-20
