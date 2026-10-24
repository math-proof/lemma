import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.IsingSharpnessUnconditional
open MeasureTheory Set StatMech StatMech.Sharpness


/--
[tildeBetaCIsingSet_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpnessUnconditional.lean)
-/
@[path]
private lemma tildeBetaCIsingSet_bddAbove_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  BddAbove (tildeBetaCIsingSet d) := by
-- proof
  apply StatMech.Sharpness.tildeBetaCIsingSet_bddAbove hd

/--
[tildeBetaCIsing_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpnessUnconditional.lean)
-/
@[path]
private lemma tildeBetaCIsing_pos_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  0 < tildeBetaCIsing d := by
-- proof
  apply StatMech.Sharpness.tildeBetaCIsing_pos hd

/--
[ising_sharpness_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpnessUnconditional.lean)
-/
@[path]
private lemma ising_sharpness_unconditional_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  (∀ beta, Ising.betaC d ≤ beta → Real.sqrt (1 - (Ising.betaC d / beta) ^ 2) ≤ magnetization d beta) ∧ (∀ beta, 0 ≤ beta → beta < Ising.betaC d → Summable (plusCorr d beta (Percolation.origin d))) ∧ (∀ beta, 0 ≤ beta → beta < Ising.betaC d → ∃ c > 0, ∀ z, plusCorr d beta (Percolation.origin d) z ≤ Real.exp (-c * (l1dist d (Percolation.origin d) z : ℝ))) := by
-- proof
  apply StatMech.Sharpness.ising_sharpness_unconditional hd


-- created on 2026-10-23
