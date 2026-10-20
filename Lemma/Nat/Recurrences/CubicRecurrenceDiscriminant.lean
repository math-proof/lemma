import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.CubicRecurrenceDiscriminant
open MetaMathlibExt


/--
[cubicRecurrenceDiscriminant_dvd_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CubicRecurrenceDiscriminant.lean)
-/
@[path]
private lemma cubicRecurrenceDiscriminant_dvd_mul_eq
  {S₁ S₂ R : ℤ}
  {U W : ℕ → ℤ}
  {n m : ℕ}
-- given
  (hseq : IsCubicRecurrencePair S₁ S₂ R U W)
  (hn : 1 ≤ n)
  (hm : 1 ≤ m) :
-- imply
  cubicRecurrenceDiscriminant R U W n ∣
    cubicRecurrenceDiscriminant R U W (n * m) := by
-- proof
  apply MetaMathlibExt.cubicRecurrenceDiscriminant_dvd_mul S₁ S₂ R U W hseq n m hn hm


-- created on 2026-10-20
