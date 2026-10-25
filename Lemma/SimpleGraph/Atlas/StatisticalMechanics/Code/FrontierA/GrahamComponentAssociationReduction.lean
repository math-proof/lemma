import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentAssociationReduction.Part3
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[couplingIn_couplingIn_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentAssociationReduction.lean)
-/
@[path]
private lemma couplingIn_couplingIn_of_subset_eq
  [Fintype V]
  [DecidableEq V]
  {S T : Finset V}
-- given
  (J : Sym2 V -> Real)
  (hST : S ⊆ T) :
-- imply
  couplingIn (couplingIn J T) S = couplingIn J S := by
-- proof
  apply StatMech.FrontierA.couplingIn_couplingIn_of_subset J hST

/--
[grahamCutPairCorrelation_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentAssociationReduction.lean)
-/
@[path]
private lemma grahamCutPairCorrelation_monotone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {x y : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  Monotone (grahamCutPairCorrelation G beta J x y) := by
-- proof
  apply StatMech.FrontierA.grahamCutPairCorrelation_monotone G beta J hbeta hJ x y

/--
[sum_isingCutMass_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentAssociationReduction.lean)
-/
@[path]
private lemma sum_isingCutMass_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {m : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  ∑ S : Finset V, isingCutMass G beta J m S = 1 := by
-- proof
  apply StatMech.FrontierA.sum_isingCutMass_eq_one G beta J m

/--
[sum_cutPairCorrelation_eq_sourcePairDisconn_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentAssociationReduction.lean)
-/
@[path]
private lemma sum_cutPairCorrelation_eq_sourcePairDisconn_div_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {x y m : V}
-- given
  (J : Sym2 V -> Real)
  (hxy : x ≠ y)
  (hxm : x ≠ m)
  (hym : y ≠ m) :
-- imply
  (∑ S : Finset V, isingCutMass G beta J m S * grahamCutPairCorrelation G beta J x y S) = sourcePairDisconnSum G beta J {x, y} ∅ x m / currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.sum_cutPairCorrelation_eq_sourcePairDisconn_div G beta J hxy hxm hym

/--
[sum_mixedComponentFiber_eq_sourcePairDisconn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentAssociationReduction.lean)
-/
@[path]
private lemma sum_mixedComponentFiber_eq_sourcePairDisconn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  (∑ S : Finset V, if j ∈ S ∧ k ∈ S ∧ l ∈ S ∧ m ∉ S then grahamSourcePairComponentFiber G beta J S m {j, k} {k, l} else 0) = sourcePairDisconnSum G beta J {j, k} {k, l} k m := by
-- proof
  apply StatMech.FrontierA.sum_mixedComponentFiber_eq_sourcePairDisconn G beta J hjk hkl

/--
[sum_cutPairCorrelation_mul_eq_mixedDisconn_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentAssociationReduction.lean)
-/
@[path]
private lemma sum_cutPairCorrelation_mul_eq_mixedDisconn_div_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  (∑ S : Finset V, isingCutMass G beta J m S * (grahamCutPairCorrelation G beta J j k S * grahamCutPairCorrelation G beta J k l S)) = sourcePairDisconnSum G beta J {j, k} {k, l} k m / currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.sum_cutPairCorrelation_mul_eq_mixedDisconn_div G beta J hjk hkl

/--
[grahamWeightedLemmaOne_of_cutPositiveAssociation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentAssociationReduction.lean)
-/
@[path]
private lemma grahamWeightedLemmaOne_of_cutPositiveAssociation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hjm : j ≠ m)
  (hkm : k ≠ m)
  (hlm : l ≠ m)
  (hassoc : GrahamCutPositiveAssociation G beta J m) :
-- imply
  sourcePairDisconnSum G beta J {j, k} ∅ k m * sourcePairDisconnSum G beta J {k, l} ∅ k m ≤ sourcePairDisconnSum G beta J {j, k} {k, l} k m * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.grahamWeightedLemmaOne_of_cutPositiveAssociation G beta J hbeta hJ hjk hkl hjm hkm hlm hassoc


-- created on 2026-10-23
