import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingGaussianIndependentDisentangling
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[finiteTreeIndependentDisjointComponentMass_le_mixedDisconnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIndependentDisentangling.lean)
-/
@[path]
private lemma finiteTreeIndependentDisjointComponentMass_le_mixedDisconnection_eq
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
  finiteTreeIndependentDisjointComponentMass G beta J i j k l <= sourcePairDisconnSum G beta J {i, j} {k, l} i k * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.finiteTreeIndependentDisjointComponentMass_le_mixedDisconnection G beta J hbeta hJ hij hkl

/--
[finiteTreeIndependentDisjointComponentMass_eq_fourMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIndependentDisentangling.lean)
-/
@[path]
private lemma finiteTreeIndependentDisjointComponentMass_eq_fourMass_eq
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
  finiteTreeIndependentDisjointComponentMass G beta J i j k l = finiteTreeIndependentDisjointFourMass G beta J i j k l := by
-- proof
  apply StatMech.FrontierA.finiteTreeIndependentDisjointComponentMass_eq_fourMass G beta J hij hkl

/--
[summable_finiteTreeIndependentDisjointSummand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIndependentDisentangling.lean)
-/
@[path]
private lemma summable_finiteTreeIndependentDisjointSummand_eq
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
  Summable (finiteTreeIndependentDisjointSummand G beta J i j k l) := by
-- proof
  apply StatMech.FrontierA.summable_finiteTreeIndependentDisjointSummand G beta J hij hkl

/--
[finiteTreeIndependentIntersection_add_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIndependentDisentangling.lean)
-/
@[path]
private lemma finiteTreeIndependentIntersection_add_disjoint_eq
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
  finiteTreeIndependentIntersectionFourMass G beta J i j k l + finiteTreeIndependentDisjointFourMass G beta J i j k l = sourcePairSum G beta J {i, j} ∅ * sourcePairSum G beta J {k, l} ∅ := by
-- proof
  apply StatMech.FrontierA.finiteTreeIndependentIntersection_add_disjoint G beta J hij hkl

/--
[finiteTreeMixedFourMass_add_disconnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIndependentDisentangling.lean)
-/
@[path]
private lemma finiteTreeMixedFourMass_add_disconnection_eq
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
  finiteTreeMixedFourMass G beta J i j k l + sourcePairDisconnSum G beta J {i, j} {k, l} i k * currentSum G beta J ∅ ^ 2 = sourcePairSum G beta J {i, j} ∅ * sourcePairSum G beta J {k, l} ∅ := by
-- proof
  apply StatMech.FrontierA.finiteTreeMixedFourMass_add_disconnection G beta J hij hkl

/--
[finiteTreeMixedFourMass_le_independentIntersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIndependentDisentangling.lean)
-/
@[path]
private lemma finiteTreeMixedFourMass_le_independentIntersection_eq
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
  apply StatMech.FrontierA.finiteTreeMixedFourMass_le_independentIntersection G beta J hbeta hJ hij hkl

/--
[finiteTreeMixedFourMass_le_sum_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIndependentDisentangling.lean)
-/
@[path]
private lemma finiteTreeMixedFourMass_le_sum_separated_eq
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
  apply StatMech.FrontierA.finiteTreeMixedFourMass_le_sum_separated G beta J hbeta hJ hij hkl

/--
[finiteIsing_treeDiagram_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIndependentDisentangling.lean)
-/
@[path]
private lemma finiteIsing_treeDiagram_bound_eq
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
  apply StatMech.FrontierA.finiteIsing_treeDiagram_bound G beta J hbeta hJ hij hik hil hjk hjl hkl


-- created on 2026-10-23
