import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianDisentanglingInequality.Part2
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[summable_finiteTreeIndependentDisjointSummand_fourCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianDisentanglingInequality.lean)
-/
@[path]
private lemma summable_finiteTreeIndependentDisjointSummand_fourCurrent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  Summable (finiteTreeIndependentDisjointSummand G beta J i j k l) := by
-- proof
  apply StatMech.FrontierA.summable_finiteTreeIndependentDisjointSummand_fourCurrent G beta J i j k l

/--
[finiteTreeIndependentDisjointFourMass_eq_componentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianDisentanglingInequality.lean)
-/
@[path]
private lemma finiteTreeIndependentDisjointFourMass_eq_componentSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (hkl : k ≠ l) :
-- imply
  finiteTreeIndependentDisjointFourCurrentMass G beta J i j k l = ∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l k, grahamFirstComponentFiber G beta J S i {i, j} ∅ * finiteTreeClusterConfinementMass G beta J k l S := by
-- proof
  apply StatMech.FrontierA.finiteTreeIndependentDisjointFourMass_eq_componentSum G beta J hij hkl

/--
[finiteTreeIndependentDisjointFourMass_le_mixedDisconnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianDisentanglingInequality.lean)
-/
@[path]
private lemma finiteTreeIndependentDisjointFourMass_le_mixedDisconnection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hij : i ≠ j)
  (hkl : k ≠ l) :
-- imply
  finiteTreeIndependentDisjointFourCurrentMass G beta J i j k l <= sourcePairDisconnSum G beta J {i, j} {k, l} i k * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.finiteTreeIndependentDisjointFourMass_le_mixedDisconnection G beta J hbeta hJ hij hkl

/--
[finiteTreeMixed_add_disconnection_eq_total](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianDisentanglingInequality.lean)
-/
@[path]
private lemma finiteTreeMixed_add_disconnection_eq_total_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (hkl : k ≠ l) :
-- imply
  finiteTreeMixedFourMass G beta J i j k l + sourcePairDisconnSum G beta J {i, j} {k, l} i k * currentSum G beta J ∅ ^ 2 = currentSum G beta J {i, j} * currentSum G beta J {k, l} * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.finiteTreeMixed_add_disconnection_eq_total G beta J hij hkl

/--
[finiteTreeIndependentIntersection_add_disjoint_eq_total](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianDisentanglingInequality.lean)
-/
@[path]
private lemma finiteTreeIndependentIntersection_add_disjoint_eq_total_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (hkl : k ≠ l) :
-- imply
  finiteTreeIndependentIntersectionFourMass G beta J i j k l + finiteTreeIndependentDisjointFourCurrentMass G beta J i j k l = currentSum G beta J {i, j} * currentSum G beta J {k, l} * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.finiteTreeIndependentIntersection_add_disjoint_eq_total G beta J hij hkl

/--
[finiteTreeMixedFourMass_le_independentIntersection_fourCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianDisentanglingInequality.lean)
-/
@[path]
private lemma finiteTreeMixedFourMass_le_independentIntersection_fourCurrent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hij : i ≠ j)
  (hkl : k ≠ l) :
-- imply
  finiteTreeMixedFourMass G beta J i j k l <= finiteTreeIndependentIntersectionFourMass G beta J i j k l := by
-- proof
  apply StatMech.FrontierA.finiteTreeMixedFourMass_le_independentIntersection_fourCurrent G beta J hbeta hJ hij hkl

/--
[finiteTreeMixedFourMass_le_sum_separated_fourCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianDisentanglingInequality.lean)
-/
@[path]
private lemma finiteTreeMixedFourMass_le_sum_separated_fourCurrent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hij : i ≠ j)
  (hkl : k ≠ l) :
-- imply
  finiteTreeMixedFourMass G beta J i j k l <= ∑ y : V, finiteTreeSeparatedFourMass G beta J i j k l y := by
-- proof
  apply StatMech.FrontierA.finiteTreeMixedFourMass_le_sum_separated_fourCurrent G beta J hbeta hJ hij hkl

/--
[finiteIsing_treeDiagram_bound_fourCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianDisentanglingInequality.lean)
-/
@[path]
private lemma finiteIsing_treeDiagram_bound_fourCurrent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  0 <= -finiteIsingFourthUrsell G beta J i j k l ∧ -finiteIsingFourthUrsell G beta J i j k l <= 2 * finiteCurrentTreeDiagram G beta J i j k l := by
-- proof
  apply StatMech.FrontierA.finiteIsing_treeDiagram_bound_fourCurrent G beta J hbeta hJ hij hik hil hjk hjl hkl


-- created on 2026-10-23
