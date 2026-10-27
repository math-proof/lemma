import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Analysis.InnerProductSpace.DiscreteSpectrum.Part2
open NonnegativeDiscreteSpectrumTest
open scoped BigOperators


namespace NonnegativeDiscreteSpectrumTest

/--
[dup_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/InnerProductSpace/DiscreteSpectrum.lean)
-/
@[path]
lemma dup_mem_iff
  {j : ℕ} :
-- imply
  dupSpectrum j < 1 ↔ j = 0 ∨ j = 1 := by
-- proof
  change dupEigen j < 1 ↔ _
  unfold dupEigen
  constructor
  · intro h
    have h1 : j / 2 < 1 := by exact_mod_cast h
    have h2 : j / 2 = 0 := Nat.lt_one_iff.mp h1
    omega
  · rintro (rfl | rfl) <;> norm_num

end NonnegativeDiscreteSpectrumTest

namespace NonnegativeDiscreteSpectrumTest

/--
[dup_sublevelFinset_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/InnerProductSpace/DiscreteSpectrum.lean)
-/
@[path]
lemma dup_sublevelFinset_one
-- imply
  dupSpectrum.sublevelFinset 1 = {0, 1} := by
-- proof
  ext j
  rw [NonnegativeDiscreteSpectrum.mem_sublevelFinset, dup_mem_iff,
    Finset.mem_insert, Finset.mem_singleton]

end NonnegativeDiscreteSpectrumTest

namespace NonnegativeDiscreteSpectrumTest

/--
[dup_counting_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/InnerProductSpace/DiscreteSpectrum.lean)
-/
@[path]
lemma dup_counting_one
-- imply
  dupSpectrum.countingFunction 1 = 2 := by
-- proof
  change (dupSpectrum.sublevelFinset 1).card = 2
  rw [dup_sublevelFinset_one]
  decide

end NonnegativeDiscreteSpectrumTest


-- created on 2026-10-23
