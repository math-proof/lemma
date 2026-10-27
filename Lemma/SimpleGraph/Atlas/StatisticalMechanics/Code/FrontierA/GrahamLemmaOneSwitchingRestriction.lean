import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamLemmaOneSwitchingRestriction
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[pair_symmDiff_shared_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamLemmaOneSwitchingRestriction.lean)
-/
@[path]
private lemma pair_symmDiff_shared_right_eq
  [Fintype V]
  [DecidableEq V]
  {j k l : V}
-- given
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  ({j, l} : Finset V) ∆ {k, l} = {j, k} := by
-- proof
  apply StatMech.FrontierA.pair_symmDiff_shared_right hjk hjl hkl

/--
[grahamMixedDisconnection_eq_connectedRestriction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamLemmaOneSwitchingRestriction.lean)
-/
@[path]
private lemma grahamMixedDisconnection_eq_connectedRestriction_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  sourcePairDisconnSum G beta J {j, k} {k, l} k m = gatedSourcePairSum G beta J {j, l} ∅ (fun n => ¬ CurrentConnected G n k m ∧ CurrentConnected G n k l) := by
-- proof
  apply StatMech.FrontierA.grahamMixedDisconnection_eq_connectedRestriction G beta J hjk hjl hkl

/--
[grahamVacuumDisconnection_eq_mixed_add_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamLemmaOneSwitchingRestriction.lean)
-/
@[path]
private lemma grahamVacuumDisconnection_eq_mixed_add_remainder_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  sourcePairDisconnSum G beta J {j, l} ∅ k m = sourcePairDisconnSum G beta J {j, k} {k, l} k m + gatedSourcePairSum G beta J {j, l} ∅ (fun n => ¬ CurrentConnected G n k m ∧ ¬ CurrentConnected G n k l) := by
-- proof
  apply StatMech.FrontierA.grahamVacuumDisconnection_eq_mixed_add_remainder G beta J hjk hjl hkl

/--
[grahamVacuumProduct_eq_mixed_add_restriction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamLemmaOneSwitchingRestriction.lean)
-/
@[path]
private lemma grahamVacuumProduct_eq_mixed_add_restriction_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  sourcePairDisconnSum G beta J {j, l} ∅ k m * currentSum G beta J ∅ ^ 2 = sourcePairDisconnSum G beta J {j, k} {k, l} k m * currentSum G beta J ∅ ^ 2 + gatedSourcePairSum G beta J {j, l} ∅ (fun n => ¬ CurrentConnected G n k m ∧ ¬ CurrentConnected G n k l) * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.grahamVacuumProduct_eq_mixed_add_restriction G beta J hjk hjl hkl

/--
[grahamMixedProduct_le_vacuumProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamLemmaOneSwitchingRestriction.lean)
-/
@[path]
private lemma grahamMixedProduct_le_vacuumProduct_eq
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
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  sourcePairDisconnSum G beta J {j, k} {k, l} k m * currentSum G beta J ∅ ^ 2 ≤ sourcePairDisconnSum G beta J {j, l} ∅ k m * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.grahamMixedProduct_le_vacuumProduct G beta J hbeta hJ hjk hjl hkl

/--
[grahamWeightedLemmaOne_iff_remainder_absorbed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamLemmaOneSwitchingRestriction.lean)
-/
@[path]
private lemma grahamWeightedLemmaOne_iff_remainder_absorbed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  sourcePairDisconnSum G beta J {j, k} ∅ k m * sourcePairDisconnSum G beta J {k, l} ∅ k m <= sourcePairDisconnSum G beta J {j, k} {k, l} k m * currentSum G beta J ∅ ^ 2 ↔ sourcePairDisconnSum G beta J {j, k} ∅ k m * sourcePairDisconnSum G beta J {k, l} ∅ k m + gatedSourcePairSum G beta J {j, l} ∅ (fun n => ¬ CurrentConnected G n k m ∧ ¬ CurrentConnected G n k l) * currentSum G beta J ∅ ^ 2 <= sourcePairDisconnSum G beta J {j, l} ∅ k m * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.grahamWeightedLemmaOne_iff_remainder_absorbed G beta J hjk hjl hkl


-- created on 2026-10-23
