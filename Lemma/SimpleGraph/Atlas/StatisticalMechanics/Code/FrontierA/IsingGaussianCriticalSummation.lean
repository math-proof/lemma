import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalSummation.Part5
open Filter Finset Set Topology StatMech StatMech.FrontierA


/--
[criticalFreeBoxSusceptibility_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean)
-/
@[path]
private lemma criticalFreeBoxSusceptibility_nonneg_eq
  {d : Nat}
  {R : Nat}
-- given
  (hd : 2 ≤ d) :
-- imply
  0 ≤ criticalFreeBoxSusceptibility d R := by
-- proof
  apply StatMech.FrontierA.criticalFreeBoxSusceptibility_nonneg hd R

/--
[one_le_criticalFreeBoxSusceptibility](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean)
-/
@[path]
private lemma one_le_criticalFreeBoxSusceptibility_eq
  {d : Nat}
  {R : Nat}
-- given
  (hd : 2 ≤ d) :
-- imply
  1 ≤ criticalFreeBoxSusceptibility d R := by
-- proof
  apply StatMech.FrontierA.one_le_criticalFreeBoxSusceptibility hd R

/--
[sum_boxSV_boxF_eq_sum_shells](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean)
-/
@[path]
private lemma sum_boxSV_boxF_eq_sum_shells_eq
  {d : Nat}
  {f : Site d → Real}
  {R : Nat} :
-- imply
  ∑ x ∈ boxSV_boxF d R, f x = f 0 + ∑ r ∈ Finset.range R, ∑ x ∈ boxSV_vbF d (r + 1), f x := by
-- proof
  apply StatMech.FrontierA.sum_boxSV_boxF_eq_sum_shells f R

/--
[exists_criticalFreeBoxSusceptibility_le_quadratic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean)
-/
@[path]
private lemma exists_criticalFreeBoxSusceptibility_le_quadratic_eq
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  ∃ A : Real, 0 < A ∧ ∀ R : Nat, criticalFreeBoxSusceptibility d R ≤ A * (R + 1 : Real) ^ 2 := by
-- proof
  apply StatMech.FrontierA.exists_criticalFreeBoxSusceptibility_le_quadratic hd

/--
[criticalRenormalizedCoupling_tendsto_zero_of_treeDiagram](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean)
-/
@[path]
private lemma criticalRenormalizedCoupling_tendsto_zero_of_treeDiagram_eq
  {d : Nat}
  {d : Nat}
  {coupling : Nat → Real}
-- given
  (hd : 4 < d)
  (htree : ∀ R, 0 ≤ coupling R ∧ coupling R ≤ criticalFreeBoxSusceptibility d R ^ 2 / (R + 1 : Real) ^ d) :
-- imply
  Tendsto coupling atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.criticalRenormalizedCoupling_tendsto_zero_of_treeDiagram d hd coupling htree

/--
[finiteDistinctIntegratedFourthCumulant_treeDiagram_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean)
-/
@[path]
private lemma finiteDistinctIntegratedFourthCumulant_treeDiagram_bound_eq
  {d : Nat}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {J : Sym2 V → Real}
  {chi : Real}
  {i : V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hchi : 0 ≤ chi)
  (hrow : ∀ y : V, ∑ x : V, expectationJ G beta J (grahamPairSupport x y) ≤ chi) :
-- imply
  0 ≤ -finiteDistinctIntegratedFourthCumulant G beta J i ∧ -finiteDistinctIntegratedFourthCumulant G beta J i ≤ 2 * chi ^ 4 := by
-- proof
  apply StatMech.FrontierA.finiteDistinctIntegratedFourthCumulant_treeDiagram_bound G beta J hbeta hJ chi hchi hrow i

/--
[criticalFiniteBoxRowSusceptibility_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean)
-/
@[path]
private lemma criticalFiniteBoxRowSusceptibility_le_eq
  {d : Nat}
  {n : Nat}
  {y : sctBox d n}
-- given
  (hd : 2 ≤ d) :
-- imply
  criticalFiniteBoxRowSusceptibility d n y ≤ criticalFreeBoxSusceptibility d (2 * n) := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxRowSusceptibility_le hd n y

/--
[criticalFiniteBoxDistinctIntegratedFourthCumulant_treeDiagram_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean)
-/
@[path]
private lemma criticalFiniteBoxDistinctIntegratedFourthCumulant_treeDiagram_bound_eq
  {d : Nat}
  {n : Nat}
  {i : sctBox d n}
-- given
  (hd : 2 ≤ d) :
-- imply
  0 ≤ -finiteDistinctIntegratedFourthCumulant (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1) i ∧ -finiteDistinctIntegratedFourthCumulant (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1) i ≤ 2 * criticalFreeBoxSusceptibility d (2 * n) ^ 4 := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxDistinctIntegratedFourthCumulant_treeDiagram_bound hd n i

/--
[criticalFiniteBoxRenormalizedFourthCoupling_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean)
-/
@[path]
private lemma criticalFiniteBoxRenormalizedFourthCoupling_bounds_eq
  {d : Nat}
  {n : Nat}
-- given
  (hd : 2 ≤ d) :
-- imply
  0 ≤ criticalFiniteBoxRenormalizedFourthCoupling d n ∧ criticalFiniteBoxRenormalizedFourthCoupling d n ≤ criticalFreeBoxSusceptibility d (2 * n) ^ 2 / ((2 * n + 1 : Nat) : Real) ^ d := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxRenormalizedFourthCoupling_bounds hd n

/--
[criticalFiniteBoxRenormalizedFourthCoupling_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean)
-/
@[path]
private lemma criticalFiniteBoxRenormalizedFourthCoupling_tendsto_zero_eq
  {d : Nat}
  {d : Nat}
-- given
  (hd : 4 < d) :
-- imply
  Tendsto (fun n => criticalFiniteBoxRenormalizedFourthCoupling d n) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxRenormalizedFourthCoupling_tendsto_zero d hd


-- created on 2026-10-23
