import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundarySwitching.Part2
open StatMech StatMech.FrontierB


/--
[sourceToggle_inter_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySwitching.lean)
-/
@[path]
private lemma sourceToggle_inter_eq_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {interior U A : Finset V}
-- given
  (hU : U ⊆ interior) :
-- imply
  (A ∆ U) ∩ interior = U ↔ A ∩ interior = ∅ := by
-- proof
  apply StatMech.FrontierB.sourceToggle_inter_eq_iff G interior U A hU

/--
[boundarySourceGatedPairSum_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySwitching.lean)
-/
@[path]
private lemma boundarySourceGatedPairSum_eq_tsum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior internalSources exactSecondSources : Finset V}
  [DecidablePred P]
-- given
  (P : Current V → Prop) :
-- imply
  boundarySourceGatedPairSum G beta J interior internalSources exactSecondSources P = ∑' pq : EdgeCurrent G × EdgeCurrent G, (if sources G (ofEdgeFun G pq.1) ∩ interior = internalSources then weight G beta J (ofEdgeFun G pq.1) else 0) * (if sources G (ofEdgeFun G pq.2) = exactSecondSources then weight G beta J (ofEdgeFun G pq.2) else 0) * (if P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) then 1 else 0) := by
-- proof
  apply StatMech.FrontierB.boundarySourceGatedPairSum_eq_tsum G beta J interior internalSources exactSecondSources P

/--
[boundarySourceCurrentSum_eq_boundarySourceSectorSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySwitching.lean)
-/
@[path]
private lemma boundarySourceCurrentSum_eq_boundarySourceSectorSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior internalSources : Finset V} :
-- imply
  boundarySourceCurrentSum G beta J interior internalSources = boundarySourceSectorSum G beta J interior internalSources := by
-- proof
  apply StatMech.FrontierB.boundarySourceCurrentSum_eq_boundarySourceSectorSum G beta J interior internalSources

/--
[boundaryCurrentSum_eq_boundarySourceCurrentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySwitching.lean)
-/
@[path]
private lemma boundaryCurrentSum_eq_boundarySourceCurrentSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V} :
-- imply
  boundaryCurrentSum G beta J interior = boundarySourceCurrentSum G beta J interior ∅ := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentSum_eq_boundarySourceCurrentSum G beta J interior

/--
[boundaryCurrentSum_eq_boundarySourceSectorSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySwitching.lean)
-/
@[path]
private lemma boundaryCurrentSum_eq_boundarySourceSectorSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V} :
-- imply
  boundaryCurrentSum G beta J interior = boundarySourceSectorSum G beta J interior ∅ := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentSum_eq_boundarySourceSectorSum G beta J interior

/--
[currentSum_le_boundarySourceCurrentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySwitching.lean)
-/
@[path]
private lemma currentSum_le_boundarySourceCurrentSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior internalSources A : Finset V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hA : A ∩ interior = internalSources) :
-- imply
  currentSum G beta J A ≤ boundarySourceCurrentSum G beta J interior internalSources := by
-- proof
  apply StatMech.FrontierB.currentSum_le_boundarySourceCurrentSum G beta J hbeta hJ interior internalSources A hA

/--
[boundarySourceCurrentSum_pos_of_currentSum_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySwitching.lean)
-/
@[path]
private lemma boundarySourceCurrentSum_pos_of_currentSum_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior internalSources A : Finset V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hA : A ∩ interior = internalSources)
  (hpos : 0 < currentSum G beta J A) :
-- imply
  0 < boundarySourceCurrentSum G beta J interior internalSources := by
-- proof
  apply StatMech.FrontierB.boundarySourceCurrentSum_pos_of_currentSum_pos G beta J hbeta hJ interior internalSources A hA hpos

/--
[boundarySourceGatedPairSum_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySwitching.lean)
-/
@[path]
private lemma boundarySourceGatedPairSum_switching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {u v : V}
  [DecidablePred P]
-- given
  (huv : u ≠ v)
  (hu : u ∈ interior)
  (hv : v ∈ interior)
  (P : Current V → Prop) :
-- imply
  boundarySourceGatedPairSum G beta J interior {u, v} {u, v} P = boundarySourceGatedPairSum G beta J interior ∅ ∅ (fun m => P m ∧ CurrentConnected G m u v) := by
-- proof
  apply StatMech.FrontierB.boundarySourceGatedPairSum_switching G beta J interior huv hu hv P


-- created on 2026-10-23
