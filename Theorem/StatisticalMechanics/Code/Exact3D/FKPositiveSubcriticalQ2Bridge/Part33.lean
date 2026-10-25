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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part34
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem copyDeleteEmbeddingDecrementFinset_not_mem_deleted
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G m)
    (K : Finset
      (Sharpness.FluxEdgeCopy.Copy G
        (Function.update m i.1 (m i.1 - 1)))) :
    i ∉ copyDeleteEmbeddingDecrementFinset G m i K := by
  intro hi
  rw [copyDeleteEmbeddingDecrementFinset, Finset.mem_map] at hi
  obtain ⟨a, _haK, hai⟩ := hi
  exact (copyDeleteEmbeddingDecrement G m i a).2 hai


theorem copyDeleteEmbeddingDecrement_degK_map
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G m)
    (K : Finset
      (Sharpness.FluxEdgeCopy.Copy G
        (Function.update m i.1 (m i.1 - 1))))
    (x : V) :
    Sharpness.RandomCurrent.degK (Sharpness.FluxEdgeCopy.endsM G m)
        (copyDeleteEmbeddingDecrementFinset G m i K) x =
      Sharpness.RandomCurrent.degK
        (Sharpness.FluxEdgeCopy.endsM G
          (Function.update m i.1 (m i.1 - 1))) K x := by
  classical
  unfold Sharpness.RandomCurrent.degK copyDeleteEmbeddingDecrementFinset
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  ext a
  simp [copyDeleteEmbeddingDecrementEmbedding_ends]


theorem copyDeleteEmbeddingDecrement_sources_map
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G m)
    (K : Finset
      (Sharpness.FluxEdgeCopy.Copy G
        (Function.update m i.1 (m i.1 - 1)))) :
    Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m)
        (copyDeleteEmbeddingDecrementFinset G m i K) =
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G
          (Function.update m i.1 (m i.1 - 1))) K := by
  ext x
  simp [Sharpness.RandomCurrent.mem_sources,
    copyDeleteEmbeddingDecrement_degK_map]


end Exact3D
end StatMech
