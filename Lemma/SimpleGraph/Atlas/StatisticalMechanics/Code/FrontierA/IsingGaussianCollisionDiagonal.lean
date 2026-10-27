import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCollisionDiagonal.Part5
open Filter Finset Set Topology StatMech StatMech.FrontierA


/--
[finiteParityFourthUrsell_eq_of_firstPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean)
-/
@[path]
private lemma finiteParityFourthUrsell_eq_of_firstPair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {J : Sym2 V → Real}
  {i k l : V} :
-- imply
  finiteParityFourthUrsell G beta J i i k l = -2 * expectationJ G beta J (grahamPairSupport i k) * expectationJ G beta J (grahamPairSupport i l) := by
-- proof
  apply StatMech.FrontierA.finiteParityFourthUrsell_eq_of_firstPair G beta J i k l

/--
[finiteParityFourthUrsell_eq_of_secondPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean)
-/
@[path]
private lemma finiteParityFourthUrsell_eq_of_secondPair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {J : Sym2 V → Real}
  {i j l : V} :
-- imply
  finiteParityFourthUrsell G beta J i j j l = -2 * expectationJ G beta J (grahamPairSupport j i) * expectationJ G beta J (grahamPairSupport j l) := by
-- proof
  apply StatMech.FrontierA.finiteParityFourthUrsell_eq_of_secondPair G beta J i j l

/--
[finiteParityFourthUrsell_eq_of_firstThird](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean)
-/
@[path]
private lemma finiteParityFourthUrsell_eq_of_firstThird_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {J : Sym2 V → Real}
  {i j l : V} :
-- imply
  finiteParityFourthUrsell G beta J i j i l = -2 * expectationJ G beta J (grahamPairSupport i j) * expectationJ G beta J (grahamPairSupport i l) := by
-- proof
  apply StatMech.FrontierA.finiteParityFourthUrsell_eq_of_firstThird G beta J i j l

/--
[finiteParityFourthUrsell_eq_of_firstFourth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean)
-/
@[path]
private lemma finiteParityFourthUrsell_eq_of_firstFourth_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {J : Sym2 V → Real}
  {i j k : V} :
-- imply
  finiteParityFourthUrsell G beta J i j k i = -2 * expectationJ G beta J (grahamPairSupport i j) * expectationJ G beta J (grahamPairSupport i k) := by
-- proof
  apply StatMech.FrontierA.finiteParityFourthUrsell_eq_of_firstFourth G beta J i j k

/--
[finiteParityFourthUrsell_eq_of_secondFourth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean)
-/
@[path]
private lemma finiteParityFourthUrsell_eq_of_secondFourth_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {J : Sym2 V → Real}
  {i j k : V} :
-- imply
  finiteParityFourthUrsell G beta J i j k j = -2 * expectationJ G beta J (grahamPairSupport j i) * expectationJ G beta J (grahamPairSupport j k) := by
-- proof
  apply StatMech.FrontierA.finiteParityFourthUrsell_eq_of_secondFourth G beta J i j k

/--
[finiteParityFourthUrsell_eq_of_thirdPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean)
-/
@[path]
private lemma finiteParityFourthUrsell_eq_of_thirdPair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {J : Sym2 V → Real}
  {i j k : V} :
-- imply
  finiteParityFourthUrsell G beta J i j k k = -2 * expectationJ G beta J (grahamPairSupport k i) * expectationJ G beta J (grahamPairSupport k j) := by
-- proof
  apply StatMech.FrontierA.finiteParityFourthUrsell_eq_of_thirdPair G beta J i j k

/--
[finiteCollisionFourthWeight_nonneg_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean)
-/
@[path]
private lemma finiteCollisionFourthWeight_nonneg_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {J : Sym2 V → Real}
  {i j k l : V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ finiteCollisionFourthWeight G beta J i j k l ∧ finiteCollisionFourthWeight G beta J i j k l ≤ finiteCollisionFourthMajorant G beta J i j k l := by
-- proof
  apply StatMech.FrontierA.finiteCollisionFourthWeight_nonneg_le G beta J hbeta hJ i j k l

/--
[finiteCollisionIntegratedFourthCumulant_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean)
-/
@[path]
private lemma finiteCollisionIntegratedFourthCumulant_le_eq
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
  0 ≤ finiteCollisionIntegratedFourthCumulant G beta J i ∧ finiteCollisionIntegratedFourthCumulant G beta J i ≤ 12 * chi ^ 2 := by
-- proof
  apply StatMech.FrontierA.finiteCollisionIntegratedFourthCumulant_le G beta J hbeta hJ chi hchi hrow i

/--
[neg_finiteParityIntegratedFourthCumulant_eq_distinct_add_collision](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean)
-/
@[path]
private lemma neg_finiteParityIntegratedFourthCumulant_eq_distinct_add_collision_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {J : Sym2 V → Real}
  {i : V} :
-- imply
  -finiteParityIntegratedFourthCumulant G beta J i = -finiteDistinctIntegratedFourthCumulant G beta J i + finiteCollisionIntegratedFourthCumulant G beta J i := by
-- proof
  apply StatMech.FrontierA.neg_finiteParityIntegratedFourthCumulant_eq_distinct_add_collision G beta J i

/--
[finiteParityIntegratedFourthCumulant_treeDiagram_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean)
-/
@[path]
private lemma finiteParityIntegratedFourthCumulant_treeDiagram_bound_eq
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
  0 ≤ -finiteParityIntegratedFourthCumulant G beta J i ∧ -finiteParityIntegratedFourthCumulant G beta J i ≤ 2 * chi ^ 4 + 12 * chi ^ 2 := by
-- proof
  apply StatMech.FrontierA.finiteParityIntegratedFourthCumulant_treeDiagram_bound G beta J hbeta hJ chi hchi hrow i

/--
[criticalFiniteBoxFullRenormalizedFourthCoupling_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean)
-/
@[path]
private lemma criticalFiniteBoxFullRenormalizedFourthCoupling_bounds_eq
  [Fintype V]
  [DecidableEq V]
  {n : Nat}
-- given
  (hd : 2 ≤ d) :
-- imply
  0 ≤ criticalFiniteBoxFullRenormalizedFourthCoupling d n ∧ criticalFiniteBoxFullRenormalizedFourthCoupling d n ≤ criticalFreeBoxSusceptibility d (2 * n) ^ 2 / ((2 * n + 1 : Nat) : Real) ^ d + 6 / ((2 * n + 1 : Nat) : Real) ^ d := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxFullRenormalizedFourthCoupling_bounds hd n

/--
[criticalFiniteBoxFullRenormalizedFourthCoupling_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean)
-/
@[path]
private lemma criticalFiniteBoxFullRenormalizedFourthCoupling_tendsto_zero_eq
  [Fintype V]
  [DecidableEq V]
  {d : Nat}
-- given
  (hd : 4 < d) :
-- imply
  Tendsto (fun n => criticalFiniteBoxFullRenormalizedFourthCoupling d n) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxFullRenormalizedFourthCoupling_tendsto_zero d hd


-- created on 2026-10-23
