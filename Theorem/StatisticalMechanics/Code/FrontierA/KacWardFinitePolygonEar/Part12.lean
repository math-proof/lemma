/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFourSignMajority
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardInteriorSideSplice
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
import Mathlib.Data.List.Rotate
import Def.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part10


namespace StatMech.FrontierA

theorem KWStraightLineCycleEarDecomposition.of_exists_removable
    (hexists : ∀ (m : ℕ) (hm : 1 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm)
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCycleEarDecomposition G embedding := by
  intro root p hp
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  rw [← embedding.cyclePolygon_edgeList p hp]
  exact KWFiniteSimplePolygon.earDecomposition_of_exists_removable_all
    hexists (embedding.cyclePolygon p hp)


theorem KWStraightLineCycleEarDecomposition.of_geometricEar_five_plus
    (hgeneric : ∀ (m : ℕ) (hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneGeometricEar (by omega))
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCycleEarDecomposition G embedding :=
  KWStraightLineCycleEarDecomposition.of_exists_removable
    (KWFiniteSimplePolygon.exists_removable_of_geometricEar_five_plus
      hgeneric) embedding


theorem KWStraightLineCycleEarDecomposition.of_alignedSideEar_five_plus
    (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneAlignedSideEar)
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCycleEarDecomposition G embedding :=
  KWStraightLineCycleEarDecomposition.of_exists_removable
    (KWFiniteSimplePolygon.exists_removable_of_alignedSideEar_five_plus
      hgeneric) embedding


theorem KWStraightLineCycleEarDecomposition.phaseProduct_eq_neg_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (h : KWStraightLineCycleEarDecomposition G embedding)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct embedding.turnPhase (kwGraphCycleDartLoop p) = -1 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  rw [← embedding.vectorPhaseCycle_of_dartLoop (kwGraphCycleDartLoop p)]
  exact (h p hp).phaseCycle_eq_neg_one

end StatMech.FrontierA
