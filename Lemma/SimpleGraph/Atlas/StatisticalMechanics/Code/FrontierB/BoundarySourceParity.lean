import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.BoundarySourceParity.Part2
open MeasureTheory StatMech StatMech.FrontierB


/--
[tsum_boundarySourceCurrentRawMass_fixedParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean)
-/
@[path]
private lemma tsum_boundarySourceCurrentRawMass_fixedParity_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior internalSources : Finset V}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  (∑' m : EdgeCurrent G, if currentParitySupport G m = H then boundarySourceCurrentRawMass G beta (fun _ ↦ 1) interior internalSources m else 0) = boundarySourceParityRawMass G beta interior internalSources H * ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
-- proof
  apply StatMech.FrontierB.tsum_boundarySourceCurrentRawMass_fixedParity G beta hbeta interior internalSources H

/--
[boundarySourceCurrentSum_eq_parityPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean)
-/
@[path]
private lemma boundarySourceCurrentSum_eq_parityPartition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior internalSources : Finset V}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  ENNReal.ofReal (boundarySourceCurrentSum G beta (fun _ ↦ 1) interior internalSources) = ENNReal.ofReal (boundarySourceParityPartition G beta interior internalSources) * ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
-- proof
  apply StatMech.FrontierB.boundarySourceCurrentSum_eq_parityPartition G beta hbeta interior internalSources

/--
[boundarySourceParityPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean)
-/
@[path]
private lemma boundarySourceParityPMF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior internalSources : Finset V}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 ≤ beta)
  (hpos : 0 < boundarySourceCurrentSum G beta (fun _ ↦ 1) interior internalSources) :
-- imply
  boundarySourceParityPMF G beta hbeta interior internalSources hpos H = boundarySourceParityRawMass G beta interior internalSources H * (ENNReal.ofReal (boundarySourceParityPartition G beta interior internalSources))⁻¹ := by
-- proof
  apply StatMech.FrontierB.boundarySourceParityPMF_apply G beta hbeta interior internalSources hpos H

/--
[boundarySourceCurrentPMF_apply_eq_parity_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean)
-/
@[path]
private lemma boundarySourceCurrentPMF_apply_eq_parity_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior internalSources : Finset V}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 < beta)
  (hpos : 0 < boundarySourceCurrentSum G beta (fun _ ↦ 1) interior internalSources) :
-- imply
  boundarySourceCurrentPMF G beta (fun _ ↦ 1) hbeta.le (fun _ ↦ zero_le_one) interior internalSources hpos m = boundarySourceParityPMF G beta hbeta.le interior internalSources hpos (currentParitySupport G m) * parityCurrentPMF G beta hbeta (currentParitySupport G m) m := by
-- proof
  apply StatMech.FrontierB.boundarySourceCurrentPMF_apply_eq_parity_factor G beta hbeta interior internalSources hpos m

/--
[boundarySourceCurrentPMF_eq_parity_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean)
-/
@[path]
private lemma boundarySourceCurrentPMF_eq_parity_bind_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior internalSources : Finset V}
-- given
  (hbeta : 0 < beta)
  (hpos : 0 < boundarySourceCurrentSum G beta (fun _ ↦ 1) interior internalSources) :
-- imply
  boundarySourceCurrentPMF G beta (fun _ ↦ 1) hbeta.le (fun _ ↦ zero_le_one) interior internalSources hpos = (boundarySourceParityPMF G beta hbeta.le interior internalSources hpos).bind (parityCurrentPMF G beta hbeta) := by
-- proof
  apply StatMech.FrontierB.boundarySourceCurrentPMF_eq_parity_bind G beta hbeta interior internalSources hpos

/--
[boundarySourceCurrentFiniteMarginal_eq_localParity_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean)
-/
@[path]
private lemma boundarySourceCurrentFiniteMarginal_eq_localParity_bind_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior internalSources : Finset V}
  {S : Finset G.edgeFinset}
-- given
  (hbeta : 0 < beta)
  (hpos : 0 < boundarySourceCurrentSum G beta (fun _ ↦ 1) interior internalSources) :
-- imply
  PMF.map (restrictCurrent S) (boundarySourceCurrentPMF G beta (fun _ ↦ 1) hbeta.le (fun _ ↦ zero_le_one) interior internalSources hpos) = (PMF.map (restrictParity G S) (boundarySourceParityPMF G beta hbeta.le interior internalSources hpos)).bind (finiteParityPMF S beta hbeta) := by
-- proof
  apply StatMech.FrontierB.boundarySourceCurrentFiniteMarginal_eq_localParity_bind G beta hbeta interior internalSources hpos S

/--
[summable_two_pow_mul_parityEdgeKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean)
-/
@[path]
private lemma summable_two_pow_mul_parityEdgeKernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {odd : Bool} :
-- imply
  Summable (fun k : ℕ ↦ (2 : ℝ) ^ k * parityEdgeKernel beta odd k) := by
-- proof
  apply StatMech.FrontierB.summable_two_pow_mul_parityEdgeKernel G beta odd

/--
[tsum_two_pow_mul_parityEdgeKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean)
-/
@[path]
private lemma tsum_two_pow_mul_parityEdgeKernel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {odd : Bool} :
-- imply
  (∑' k : ℕ, (2 : ℝ) ^ k * parityEdgeKernel beta odd k) = if odd then Real.sinh (2 * beta) / Real.sinh beta else Real.cosh (2 * beta) / Real.cosh beta := by
-- proof
  apply StatMech.FrontierB.tsum_two_pow_mul_parityEdgeKernel G beta odd

/--
[tsum_two_pow_mul_parityEdgeKernel_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean)
-/
@[path]
private lemma tsum_two_pow_mul_parityEdgeKernel_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {odd : Bool}
-- given
  (hbeta : 0 < beta) :
-- imply
  (∑' k : ℕ, (2 : ℝ) ^ k * parityEdgeKernel beta odd k) ≤ 2 * Real.exp beta := by
-- proof
  apply StatMech.FrontierB.tsum_two_pow_mul_parityEdgeKernel_le G beta hbeta odd

/--
[tsum_parityEdgeKernel_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean)
-/
@[path]
private lemma tsum_parityEdgeKernel_tail_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {odd : Bool}
  {K : ℕ}
-- given
  (hbeta : 0 < beta) :
-- imply
  (∑' k : ℕ, if K ≤ k then parityEdgeKernel beta odd k else 0) ≤ 2 * Real.exp beta / (2 : ℝ) ^ K := by
-- proof
  apply StatMech.FrontierB.tsum_parityEdgeKernel_tail_le G beta hbeta odd K

/--
[summable_parityCurrentKernel_edge_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean)
-/
@[path]
private lemma summable_parityCurrentKernel_edge_tail_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {H : Finset (Sym2 V)}
  {e : G.edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 < beta) :
-- imply
  Summable (fun m : EdgeCurrent G ↦ if K ≤ m e then parityCurrentKernel G beta H m else 0) := by
-- proof
  apply StatMech.FrontierB.summable_parityCurrentKernel_edge_tail G beta hbeta H e K

/--
[tsum_parityCurrentKernel_edge_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean)
-/
@[path]
private lemma tsum_parityCurrentKernel_edge_tail_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {H : Finset (Sym2 V)}
  {e : G.edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 < beta) :
-- imply
  (∑' m : EdgeCurrent G, if K ≤ m e then parityCurrentKernel G beta H m else 0) = ∑' k : ℕ, if K ≤ k then parityEdgeKernel beta (e.1 ∈ H) k else 0 := by
-- proof
  apply StatMech.FrontierB.tsum_parityCurrentKernel_edge_tail G beta hbeta H e K

/--
[parityCurrentPMF_edge_exponential_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean)
-/
@[path]
private lemma parityCurrentPMF_edge_exponential_tail_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {H : Finset (Sym2 V)}
  {e : G.edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 < beta) :
-- imply
  (parityCurrentPMF G beta hbeta H).toMeasure {m | K ≤ m e} ≤ ENNReal.ofReal (2 * Real.exp beta / (2 : ℝ) ^ K) := by
-- proof
  apply StatMech.FrontierB.parityCurrentPMF_edge_exponential_tail_le G beta hbeta H e K

/--
[parityCurrentPMF_edge_inverse_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean)
-/
@[path]
private lemma parityCurrentPMF_edge_inverse_tail_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {H : Finset (Sym2 V)}
  {e : G.edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 < beta)
  (hK : 0 < K) :
-- imply
  (parityCurrentPMF G beta hbeta H).toMeasure {m | K ≤ m e} ≤ ENNReal.ofReal (2 * Real.exp beta / K) := by
-- proof
  apply StatMech.FrontierB.parityCurrentPMF_edge_inverse_tail_le G beta hbeta H e K hK

/--
[boundarySourceCurrentPMF_edge_exponential_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean)
-/
@[path]
private lemma boundarySourceCurrentPMF_edge_exponential_tail_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior internalSources : Finset V}
  {e : G.edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 < beta)
  (hpos : 0 < boundarySourceCurrentSum G beta (fun _ ↦ 1) interior internalSources) :
-- imply
  (boundarySourceCurrentPMF G beta (fun _ ↦ 1) hbeta.le (fun _ ↦ zero_le_one) interior internalSources hpos).toMeasure {m | K ≤ m e} ≤ ENNReal.ofReal (2 * Real.exp beta / (2 : ℝ) ^ K) := by
-- proof
  apply StatMech.FrontierB.boundarySourceCurrentPMF_edge_exponential_tail_le G beta hbeta interior internalSources hpos e K

/--
[boundarySourceCurrentPMF_edge_inverse_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean)
-/
@[path]
private lemma boundarySourceCurrentPMF_edge_inverse_tail_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior internalSources : Finset V}
  {e : G.edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 < beta)
  (hpos : 0 < boundarySourceCurrentSum G beta (fun _ ↦ 1) interior internalSources)
  (hK : 0 < K) :
-- imply
  (boundarySourceCurrentPMF G beta (fun _ ↦ 1) hbeta.le (fun _ ↦ zero_le_one) interior internalSources hpos).toMeasure {m | K ≤ m e} ≤ ENNReal.ofReal (2 * Real.exp beta / K) := by
-- proof
  apply StatMech.FrontierB.boundarySourceCurrentPMF_edge_inverse_tail_le G beta hbeta interior internalSources hpos e K hK


-- created on 2026-10-23
