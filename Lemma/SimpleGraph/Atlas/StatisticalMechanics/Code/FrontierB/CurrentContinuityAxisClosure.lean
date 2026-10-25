import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityAxisClosure
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[freeInfiniteVolume_noPercolation_of_currentContinuityFreeAxisLROZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityAxisClosure.lean)
-/
@[path]
private lemma freeInfiniteVolume_noPercolation_of_currentContinuityFreeAxisLROZero_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (hLRO : CurrentContinuityFreeAxisLROZero d hd beta) :
-- imply
  (freeInfiniteVolume d (p := 1 - Real.exp (-2 * beta)) (q := 2) (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))) (by linarith [Real.exp_pos (-2 * beta)]) (by norm_num : (0 : Real) < 2) : Measure _).real (percolationEvent d) = 0 := by
-- proof
  apply StatMech.FrontierB.freeInfiniteVolume_noPercolation_of_currentContinuityFreeAxisLROZero beta hbeta hd hLRO

/--
[currentContinuity_magnetization_and_phase_eq_of_freeAxisLROZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityAxisClosure.lean)
-/
@[path]
private lemma currentContinuity_magnetization_and_phase_eq_of_freeAxisLROZero_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (hLRO : CurrentContinuityFreeAxisLROZero d hd beta) :
-- imply
  (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real (percolationEvent d) = 0 ∧ (freeInfiniteVolume d (p := 1 - Real.exp (-2 * beta)) (q := 2) (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))) (by linarith [Real.exp_pos (-2 * beta)]) (by norm_num : (0 : Real) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) = (wiredInfiniteVolume d (p := 1 - Real.exp (-2 * beta)) (q := 2) (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))) (by linarith [Real.exp_pos (-2 * beta)]) (by norm_num : (0 : Real) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) ∧ magnetization d beta = 0 ∧ (plusState d beta 0 : Measure (ConfigSpace (Site d))) = (minusState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.currentContinuity_magnetization_and_phase_eq_of_freeAxisLROZero beta hbeta hd hLRO


-- created on 2026-10-23
