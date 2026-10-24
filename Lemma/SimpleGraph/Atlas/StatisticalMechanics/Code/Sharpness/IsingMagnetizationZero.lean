import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.IsingMagnetizationZero
open MeasureTheory Filter Topology BoundedContinuousFunction StatMech StatMech.Sharpness


/--
[magnetization_sq_le_plusCorr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingMagnetizationZero.lean)
-/
@[path]
private lemma magnetization_sq_le_plusCorr_eq
  {d : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  magnetization d beta ^ 2 ≤ plusCorr d beta x y := by
-- proof
  apply StatMech.Sharpness.magnetization_sq_le_plusCorr beta hbeta x y

/--
[magnetization_eq_zero_of_plusCorr_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingMagnetizationZero.lean)
-/
@[path]
private lemma magnetization_eq_zero_of_plusCorr_summable_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 ≤ beta)
  (hsum : Summable (plusCorr d beta (Percolation.origin d))) :
-- imply
  magnetization d beta = 0 := by
-- proof
  apply StatMech.Sharpness.magnetization_eq_zero_of_plusCorr_summable hd beta hbeta hsum

/--
[bc_eq_ising_of_sqrt_and_susceptibility](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingMagnetizationZero.lean)
-/
@[path]
private lemma bc_eq_ising_of_sqrt_and_susceptibility_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (hsqrt : ∀ beta, tildeBetaCIsing d ≤ beta → Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤ magnetization d beta) :
-- imply
  betaC d = tildeBetaCIsing d := by
-- proof
  apply StatMech.Sharpness.bc_eq_ising_of_sqrt_and_susceptibility hd hsqrt


-- created on 2026-10-23
