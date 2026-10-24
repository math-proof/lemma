import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.BoundaryCurrentParity
open MeasureTheory StatMech StatMech.FrontierB


/--
[boundaryPartitionJ_high_temp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentParity.lean)
-/
@[path]
private lemma boundaryPartitionJ_high_temp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V} :
-- imply
  boundaryPartitionJ G beta J interior = (2 : ℝ) ^ interior.card * (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) * ∑ H ∈ G.edgeFinset.powerset, if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ then highTempSubgraphWeight beta J H else 0 := by
-- proof
  apply StatMech.FrontierB.boundaryPartitionJ_high_temp G beta J interior

/--
[boundaryPartitionJ_unit_high_temp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentParity.lean)
-/
@[path]
private lemma boundaryPartitionJ_unit_high_temp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior : Finset V} :
-- imply
  boundaryPartitionJ G beta (fun _ => 1) interior = (2 : ℝ) ^ interior.card * Real.cosh beta ^ G.edgeFinset.card * boundaryParityPartition G beta interior := by
-- proof
  apply StatMech.FrontierB.boundaryPartitionJ_unit_high_temp G beta interior

/--
[boundaryPartitionJ_deleted_high_temp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentParity.lean)
-/
@[path]
private lemma boundaryPartitionJ_deleted_high_temp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior : Finset V}
  {F : Finset (Sym2 V)}
-- given
  (hF : F ⊆ G.edgeFinset) :
-- imply
  boundaryPartitionJ G beta (deletedEdgeCoupling F) interior = (2 : ℝ) ^ interior.card * Real.cosh beta ^ (G.edgeFinset.card - F.card) * boundaryParityAvoidSum G beta interior F := by
-- proof
  apply StatMech.FrontierB.boundaryPartitionJ_deleted_high_temp G beta interior F hF

/--
[tsum_boundaryCurrentRawMass_fixedParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentParity.lean)
-/
@[path]
private lemma tsum_boundaryCurrentRawMass_fixedParity_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior : Finset V}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  (∑' m : EdgeCurrent G, if currentParitySupport G m = H then boundaryCurrentRawMass G beta (fun _ => 1) interior m else 0) = boundaryParityRawMass G beta interior H * ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
-- proof
  apply StatMech.FrontierB.tsum_boundaryCurrentRawMass_fixedParity G beta hbeta interior H

/--
[boundaryCurrentSum_eq_boundaryParityPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentParity.lean)
-/
@[path]
private lemma boundaryCurrentSum_eq_boundaryParityPartition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior : Finset V}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  ENNReal.ofReal (boundaryCurrentSum G beta (fun _ => 1) interior) = ENNReal.ofReal (boundaryParityPartition G beta interior) * ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentSum_eq_boundaryParityPartition G beta hbeta interior

/--
[boundaryParityPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentParity.lean)
-/
@[path]
private lemma boundaryParityPMF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior : Finset V}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  boundaryParityPMF G beta hbeta interior H = boundaryParityRawMass G beta interior H * (ENNReal.ofReal (boundaryParityPartition G beta interior))⁻¹ := by
-- proof
  apply StatMech.FrontierB.boundaryParityPMF_apply G beta hbeta interior H

/--
[boundaryParityPartition_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentParity.lean)
-/
@[path]
private lemma boundaryParityPartition_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior : Finset V}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  0 < boundaryParityPartition G beta interior := by
-- proof
  apply StatMech.FrontierB.boundaryParityPartition_pos G beta hbeta interior

/--
[boundaryParityMeasure_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentParity.lean)
-/
@[path]
private lemma boundaryParityMeasure_avoid_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior : Finset V}
  {F : Finset (Sym2 V)}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  (boundaryParityPMF G beta hbeta interior).toMeasure {H | Disjoint H F} = ENNReal.ofReal (boundaryParityAvoidSum G beta interior F / boundaryParityPartition G beta interior) := by
-- proof
  apply StatMech.FrontierB.boundaryParityMeasure_avoid G beta hbeta interior F

/--
[boundaryParityAvoidRatio_eq_spinExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentParity.lean)
-/
@[path]
private lemma boundaryParityAvoidRatio_eq_spinExpectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior : Finset V}
  {F : Finset (Sym2 V)}
-- given
  (hF : F ⊆ G.edgeFinset) :
-- imply
  boundaryParityAvoidSum G beta interior F / boundaryParityPartition G beta interior = ((∑ s : ConfigSpace ↑interior, boltzmannJ G beta (fun _ => 1) (extendInteriorPlus interior s) * Real.exp (-beta * edgeSpinSum F (extendInteriorPlus interior s))) / boundaryPartitionJ G beta (fun _ => 1) interior) * Real.cosh beta ^ F.card := by
-- proof
  apply StatMech.FrontierB.boundaryParityAvoidRatio_eq_spinExpectation G beta interior F hF

/--
[boundaryParityMeasure_avoid_eq_spinExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentParity.lean)
-/
@[path]
private lemma boundaryParityMeasure_avoid_eq_spinExpectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior : Finset V}
  {F : Finset (Sym2 V)}
-- given
  (hbeta : 0 ≤ beta)
  (hF : F ⊆ G.edgeFinset) :
-- imply
  (boundaryParityPMF G beta hbeta interior).toMeasure {H | Disjoint H F} = ENNReal.ofReal (((∑ s : ConfigSpace ↑interior, boltzmannJ G beta (fun _ => 1) (extendInteriorPlus interior s) * Real.exp (-beta * edgeSpinSum F (extendInteriorPlus interior s))) / boundaryPartitionJ G beta (fun _ => 1) interior) * Real.cosh beta ^ F.card) := by
-- proof
  apply StatMech.FrontierB.boundaryParityMeasure_avoid_eq_spinExpectation G beta hbeta interior F hF

/--
[boundaryCurrentPMF_apply_eq_parity_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentParity.lean)
-/
@[path]
private lemma boundaryCurrentPMF_apply_eq_parity_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior : Finset V}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 < beta) :
-- imply
  boundaryCurrentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) interior m = boundaryParityPMF G beta hbeta.le interior (currentParitySupport G m) * parityCurrentPMF G beta hbeta (currentParitySupport G m) m := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentPMF_apply_eq_parity_factor G beta hbeta interior m

/--
[boundaryCurrentPMF_eq_parity_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentParity.lean)
-/
@[path]
private lemma boundaryCurrentPMF_eq_parity_bind_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior : Finset V}
-- given
  (hbeta : 0 < beta) :
-- imply
  boundaryCurrentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) interior = (boundaryParityPMF G beta hbeta.le interior).bind (parityCurrentPMF G beta hbeta) := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentPMF_eq_parity_bind G beta hbeta interior

/--
[boundaryCurrentFiniteMarginal_eq_localParity_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentParity.lean)
-/
@[path]
private lemma boundaryCurrentFiniteMarginal_eq_localParity_bind_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior : Finset V}
  {S : Finset G.edgeFinset}
-- given
  (hbeta : 0 < beta) :
-- imply
  PMF.map (restrictCurrent S) (boundaryCurrentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) interior) = (PMF.map (restrictParity G S) (boundaryParityPMF G beta hbeta.le interior)).bind (finiteParityPMF S beta hbeta) := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentFiniteMarginal_eq_localParity_bind G beta hbeta interior S


-- created on 2026-10-23
