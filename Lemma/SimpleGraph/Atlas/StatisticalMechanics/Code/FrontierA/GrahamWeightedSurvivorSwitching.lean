import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedSurvivorSwitching
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[gatedSourcePairSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedSurvivorSwitching.lean)
-/
@[path]
private lemma gatedSourcePairSum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A B : Finset V}
  [DecidablePred P]
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (P : Current V -> Prop) :
-- imply
  0 ≤ gatedSourcePairSum G beta J A B P := by
-- proof
  apply StatMech.FrontierA.gatedSourcePairSum_nonneg G beta J hbeta hJ A B P

/--
[gatedSourcePairSum_mono_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedSurvivorSwitching.lean)
-/
@[path]
private lemma gatedSourcePairSum_mono_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A B : Finset V}
  [DecidablePred P]
  [DecidablePred Q]
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (P Q : Current V -> Prop)
  (hPQ : ∀ p q : G.edgeFinset -> Nat, sources G (ofEdgeFun G p) = A -> sources G (ofEdgeFun G q) = B -> P (ofEdgeFun G (fun e => p e + q e)) -> Q (ofEdgeFun G (fun e => p e + q e))) :
-- imply
  gatedSourcePairSum G beta J A B P ≤ gatedSourcePairSum G beta J A B Q := by
-- proof
  apply StatMech.FrontierA.gatedSourcePairSum_mono_sources G beta J hbeta hJ A B P Q hPQ

/--
[grahamFirstSurvivor_switching_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedSurvivorSwitching.lean)
-/
@[path]
private lemma grahamFirstSurvivor_switching_lower_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k) :
-- imply
  gatedSourcePairSum G beta J {i, k} {k, j} (fun n => ¬ CurrentConnected G n i m) ≤ gatedSourcePairSum G beta J {i, j} ∅ (fun n => ¬ CurrentConnected G n i m ∧ (CurrentConnected G n i k ∨ CurrentConnected G n i l)) := by
-- proof
  apply StatMech.FrontierA.grahamFirstSurvivor_switching_lower_bound G beta J hbeta hJ hij hik hjk

/--
[grahamSecondSurvivor_switching_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedSurvivorSwitching.lean)
-/
@[path]
private lemma grahamSecondSurvivor_switching_lower_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hik : i ≠ k)
  (hkl : k ≠ l)
  (hil : i ≠ l) :
-- imply
  gatedSourcePairSum G beta J {k, i} {i, l} (fun n => ¬ CurrentConnected G n k m) ≤ gatedSourcePairSum G beta J {k, l} ∅ (fun n => ¬ CurrentConnected G n k m ∧ (CurrentConnected G n k i ∨ CurrentConnected G n k j)) := by
-- proof
  apply StatMech.FrontierA.grahamSecondSurvivor_switching_lower_bound G beta J hbeta hJ hik hkl hil


-- created on 2026-10-23
