import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedSimonComparison
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamPinnedSimonComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedSimonComparison.lean)
-/
@[path]
private lemma grahamPinnedSimonComparison_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (hJ : ∀ e, 0 <= J e)
  (hjm : j ≠ m)
  (hkm : k ≠ m)
  (hlm : l ≠ m) :
-- imply
  (1 - grahamTwoPoint E J k m ^ 2) * grahamBridgeGap E J j l m <= grahamTwoPoint E J j l - grahamFourPoint E J j l k m * grahamTwoPoint E J k m := by
-- proof
  apply StatMech.FrontierA.grahamPinnedSimonComparison E J hdiag hJ hjm hkm hlm

/--
[expectationSwitchingGap_eq_sourcePairDisconn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedSimonComparison.lean)
-/
@[path]
private lemma expectationSwitchingGap_eq_sourcePairDisconn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A : Finset V}
  {u v : V}
-- given
  (J : Sym2 V -> Real)
  (huv : u ≠ v) :
-- imply
  expectationJ G beta J A - expectationJ G beta J (A ∆ {u, v}) * expectationJ G beta J {u, v} = sourcePairDisconnSum G beta J A ∅ u v / currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.expectationSwitchingGap_eq_sourcePairDisconn G beta J A huv

/--
[grahamPinnedSimonComparison_le_fullDisconnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedSimonComparison.lean)
-/
@[path]
private lemma grahamPinnedSimonComparison_le_fullDisconnection_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (hJ : ∀ e, 0 <= J e)
  (hjl : j ≠ l)
  (hjm : j ≠ m)
  (hkm : k ≠ m)
  (hlm : l ≠ m) :
-- imply
  (1 - grahamTwoPoint E J k m ^ 2) * grahamBridgeGap E J j l m <= sourcePairDisconnSum (grahamGraph E) 1 J {j, l} ∅ k m / currentSum (grahamGraph E) 1 J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.grahamPinnedSimonComparison_le_fullDisconnection E J hdiag hJ hjl hjm hkm hlm

/--
[grahamBridgeProduct_le_fullDisconnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedSimonComparison.lean)
-/
@[path]
private lemma grahamBridgeProduct_le_fullDisconnection_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (hJ : ∀ e, 0 <= J e)
  (hjl : j ≠ l)
  (hjm : j ≠ m)
  (hkm : k ≠ m)
  (hlm : l ≠ m) :
-- imply
  grahamBridgeGap E J j k m * grahamBridgeGap E J l k m <= sourcePairDisconnSum (grahamGraph E) 1 J {j, l} ∅ k m / currentSum (grahamGraph E) 1 J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.grahamBridgeProduct_le_fullDisconnection E J hdiag hJ hjl hjm hkm hlm


-- created on 2026-10-23
