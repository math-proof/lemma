/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part31
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostBoundaryCrossingPairs_mem
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) :
    p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v ↔
      p.1 ∈ finiteBoundaryGhostSourceSector m ∧
      p.2 ∈ p.1 ∧
      some v ∈ Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 ∧
      none ∈ Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 := by
  classical
  rw [finiteBoundaryGhostBoundaryCrossingPairs, Finset.mem_sigma]
  simp


theorem finiteBoundaryGhostBoundaryCrossingPairs_card
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    (finiteBoundaryGhostBoundaryCrossingPairs m v).card =
      finiteBoundaryGhostBoundaryCrossingPairCount m v := by
  classical
  rw [finiteBoundaryGhostBoundaryCrossingPairs, Finset.card_sigma]
  rfl


theorem finiteBoundaryGhostBoundaryCrossingPairCountSummand_eq_sum_pairs
    {β H : ℝ} {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    ((if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n then
        (1 : ℝ)
      else
        0) *
      (finiteBoundaryGhostBoundaryCrossingPairCount m v : ℝ)) *
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) =
      ∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
        (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) := by
  classical
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  rw [finiteBoundaryGhostBoundaryCrossingPairs_card]
  ring


theorem finiteBoundaryGhostBoundaryCrossingSourceSector_card_le_crossingPairCount_nat
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    (finiteBoundaryGhostBoundaryCrossingSourceSector m v).card ≤
      finiteBoundaryGhostBoundaryCrossingPairCount m v := by
  classical
  rw [finiteBoundaryGhostBoundaryCrossingSourceSector]
  unfold finiteBoundaryGhostBoundaryCrossingPairCount
  rw [Finset.card_filter]
  refine Finset.sum_le_sum ?_
  intro K hK
  by_cases hcross :
      ∃ i ∈ K,
        some v ∈ Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧
        none ∈ Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m i
  · have hpos :
        0 < finiteBoundaryGhostBoundaryCrossingCopyCount m v K := by
      rw [finiteBoundaryGhostBoundaryCrossingCopyCount, Finset.card_pos]
      obtain ⟨i, hiK, hsome, hnone⟩ := hcross
      exact ⟨i, by simp [hiK, hsome, hnone]⟩
    have hle :
        1 ≤ finiteBoundaryGhostBoundaryCrossingCopyCount m v K :=
      Nat.succ_le_of_lt hpos
    simpa [hcross] using hle
  · simp [hcross]


theorem finiteBoundaryGhostBoundaryCrossingSourceSector_card_le_crossingPairCount
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card : ℝ) ≤
      (finiteBoundaryGhostBoundaryCrossingPairCount m v : ℝ) := by
  exact_mod_cast
    finiteBoundaryGhostBoundaryCrossingSourceSector_card_le_crossingPairCount_nat
      m v


theorem edgeCopy_filter_card_le_multiplicity_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy G m))
    (P : ↥G.edgeFinset → Prop) [DecidablePred P] :
    (K.filter (fun i => P i.1)).card ≤
      ∑ e : ↥G.edgeFinset, if P e then m e else 0 := by
  classical
  have hsub :
      K.filter (fun i => P i.1) ⊆
        ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)).filter
          (fun i => P i.1)) := by
    intro i hi
    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
  refine (Finset.card_le_card hsub).trans_eq ?_
  have hcard :
      ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)).filter
        (fun i => P i.1)).card =
        ∑ i : Sharpness.FluxEdgeCopy.Copy G m,
          if P i.1 then 1 else 0 := by
    rw [Finset.card_filter]
  rw [hcard, Fintype.sum_sigma]
  refine Finset.sum_congr rfl ?_
  intro e _he
  by_cases hP : P e
  · rw [if_pos hP]
    simp [hP, Fintype.card_fin]
  · rw [if_neg hP]
    simp [hP]


end Exact3D
end StatMech
