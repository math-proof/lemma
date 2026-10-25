import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCutPairAssociation
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamCutPairAssociationAt_of_cutPositiveAssociation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutPairAssociation.lean)
-/
@[path]
private lemma grahamCutPairAssociationAt_of_cutPositiveAssociation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e)
  (hassoc : GrahamCutPositiveAssociation G beta J m) :
-- imply
  GrahamCutPairAssociationAt G beta J j k l m := by
-- proof
  apply StatMech.FrontierA.grahamCutPairAssociationAt_of_cutPositiveAssociation G beta J hbeta hJ j k l m hassoc

/--
[grahamCutPairAssociationAt_of_fourFunctions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutPairAssociation.lean)
-/
@[path]
private lemma grahamCutPairAssociationAt_of_fourFunctions_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e)
  (hfour : forall A B : Finset V, (isingCutMass G beta J m A * grahamCutPairCorrelation G beta J j k A) * (isingCutMass G beta J m B * grahamCutPairCorrelation G beta J k l B) <= isingCutMass G beta J m (A ∩ B) * (isingCutMass G beta J m (A ∪ B) * (grahamCutPairCorrelation G beta J j k (A ∪ B) * grahamCutPairCorrelation G beta J k l (A ∪ B)))) :
-- imply
  GrahamCutPairAssociationAt G beta J j k l m := by
-- proof
  apply StatMech.FrontierA.grahamCutPairAssociationAt_of_fourFunctions G beta J hbeta hJ j k l m hfour

/--
[grahamCutPairAssociationAt_iff_weightedLemmaOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutPairAssociation.lean)
-/
@[path]
private lemma grahamCutPairAssociationAt_iff_weightedLemmaOne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hjk : Ne j k)
  (hkl : Ne k l)
  (hjm : Ne j m)
  (hkm : Ne k m)
  (hlm : Ne l m) :
-- imply
  GrahamCutPairAssociationAt G beta J j k l m <-> sourcePairDisconnSum G beta J {j, k} ∅ k m * sourcePairDisconnSum G beta J {k, l} ∅ k m <= sourcePairDisconnSum G beta J {j, k} {k, l} k m * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.grahamCutPairAssociationAt_iff_weightedLemmaOne G beta J hjk hkl hjm hkm hlm


-- created on 2026-10-23
