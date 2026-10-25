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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part54
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_mem
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (a : Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)) :
    a ∈
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
          n Ω v ↔
      a.1 ∈ Ω := by
  classical
  unfold finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
  constructor
  · intro ha
    rcases Finset.mem_map.mp ha with ⟨b, hb, hbmap⟩
    have hbΩ : b.1.1 ∈ Ω := b.1.2
    have hfst : b.1.1 = a.1 := by
      simpa [
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupportEmbedding]
        using congrArg Sigma.fst hbmap
    simpa [← hfst] using hbΩ
  · intro ha
    refine Finset.mem_map.mpr ?_
    refine ⟨⟨⟨a.1, ha⟩, a.2⟩, ?_, rfl⟩
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_attach _ ⟨a.1, ha⟩, Finset.mem_univ _⟩


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexFiber_univ_sum_eq_pair_sum
    (β H : ℝ) {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    (∑ p : finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v,
        finiteBoundaryGhostDecrementedSourceWeightVertexFiberSummand
          β H n m v p) =
      Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v)
        (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
          β H m v) := by
  classical
  unfold finiteBoundaryGhostDecrementedSourceWeightVertexFiberSummand
  change
    (∑ p ∈ (Finset.univ :
        Finset
          (finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)),
        finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
          β H m v p.1) =
      Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v)
        (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
          β H m v)
  rw [Finset.univ_eq_attach
    (finiteBoundaryGhostBoundaryCrossingPairs m v)]
  exact
    Finset.sum_attach
      (finiteBoundaryGhostBoundaryCrossingPairs m v)
      (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
        β H m v)


theorem finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_attach_sum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v =
      ∑ m ∈ Ω.attach,
        Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m.1 v)
          (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
            β H m.1 v) := by
  classical
  unfold finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
  exact
    (Finset.sum_attach Ω
      (fun m =>
        Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v)
          (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
            β H m v))).symm


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_vertexCutoffSum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (∑ a ∈
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
          n Ω v,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a) =
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
        β H n Ω v := by
  classical
  unfold finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
  rw [Finset.sum_map, Finset.sum_sigma]
  calc
    (∑ m ∈ Ω.attach,
        ∑ p ∈ (Finset.univ :
          Finset
            (finiteBoundaryGhostDecrementedSourceWeightVertexFiber
              n m.1 v)),
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
            β H n v
            ((finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupportEmbedding
              n Ω v) ⟨m, p⟩))
        =
      ∑ m ∈ Ω.attach,
        Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m.1 v)
          (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
            β H m.1 v) := by
      refine Finset.sum_congr rfl ?_
      intro m _hm
      change
        (∑ p : finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m.1 v,
          finiteBoundaryGhostDecrementedSourceWeightVertexFiberSummand
            β H n m.1 v p) =
          Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m.1 v)
            (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
              β H m.1 v)
      exact
        finiteBoundaryGhostDecrementedSourceWeightVertexFiber_univ_sum_eq_pair_sum
          β H m.1 v
    _ =
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
        β H n Ω v :=
      (finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_attach_sum
        β H n Ω v).symm


end Exact3D
end StatMech
