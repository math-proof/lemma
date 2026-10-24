import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingGaussianFourCurrentTree
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[finiteTreeMixedFourMass_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourCurrentTree.lean)
-/
@[path]
private lemma finiteTreeMixedFourMass_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  finiteTreeMixedFourMass G beta J i j k l = gatedSourcePairSum G beta J (grahamPairSupport i j) (grahamPairSupport k l) (fun n => CurrentConnected G n i k) * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.finiteTreeMixedFourMass_eq G beta J i j k l

/--
[finiteTreeMixedFourMass_eq_allThree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourCurrentTree.lean)
-/
@[path]
private lemma finiteTreeMixedFourMass_eq_allThree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  finiteTreeMixedFourMass G beta J i j k l = gatedSourcePairSum G beta J {i, j, k, l} ∅ (fun n => grahamAllThreeConnected G n i j k l) * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.finiteTreeMixedFourMass_eq_allThree G beta J hij hik hil hjk hjl hkl

/--
[finiteTreeSeparatedFourMass_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourCurrentTree.lean)
-/
@[path]
private lemma finiteTreeSeparatedFourMass_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l y : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  finiteTreeSeparatedFourMass G beta J i j k l y = gatedSourcePairSum G beta J (grahamPairSupport i j) ∅ (fun n => CurrentConnected G n i y) * gatedSourcePairSum G beta J (grahamPairSupport k l) ∅ (fun n => CurrentConnected G n k y) := by
-- proof
  apply StatMech.FrontierA.finiteTreeSeparatedFourMass_eq G beta J i j k l y

/--
[finiteTreeSeparatedFourMass_eq_twoPointMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourCurrentTree.lean)
-/
@[path]
private lemma finiteTreeSeparatedFourMass_eq_twoPointMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l y : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  finiteTreeSeparatedFourMass G beta J i j k l y = currentSum G beta J (grahamPairSupport i y) * currentSum G beta J (grahamPairSupport j y) * currentSum G beta J (grahamPairSupport k y) * currentSum G beta J (grahamPairSupport l y) := by
-- proof
  apply StatMech.FrontierA.finiteTreeSeparatedFourMass_eq_twoPointMass G beta J i j k l y

/--
[sum_finiteTreeSeparatedFourMass_eq_treeDiagramMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourCurrentTree.lean)
-/
@[path]
private lemma sum_finiteTreeSeparatedFourMass_eq_treeDiagramMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  ∑ y : V, finiteTreeSeparatedFourMass G beta J i j k l y = finiteCurrentTreeDiagramMass G beta J i j k l := by
-- proof
  apply StatMech.FrontierA.sum_finiteTreeSeparatedFourMass_eq_treeDiagramMass G beta J i j k l


-- created on 2026-10-23
