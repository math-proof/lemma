/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part12
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnitCycleReduction
import Def.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction
open scoped BigOperators
open Finset SimpleGraph Polynomial


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Ising

universe u


theorem KWStraightLineCycleEarDecomposition.toPhaseSign
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (h : KWStraightLineCycleEarDecomposition G embedding) :
    KWStraightLineCyclePhaseSign G embedding := by
  intro root p hp
  exact h.phaseProduct_eq_neg_one p hp


theorem KWStraightLineCyclePhaseSign.of_exists_removable
    (hexists : ∀ (m : ℕ) (hm : 1 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm)
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCyclePhaseSign G embedding :=
  KWStraightLineCycleEarDecomposition.toPhaseSign
    (KWStraightLineCycleEarDecomposition.of_exists_removable
      hexists embedding)


theorem KWStraightLineCyclePhaseSign.of_geometricEar_five_plus
    (hgeneric : ∀ (m : ℕ) (hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneGeometricEar (by omega))
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCyclePhaseSign G embedding :=
  KWStraightLineCycleEarDecomposition.toPhaseSign
    (KWStraightLineCycleEarDecomposition.of_geometricEar_five_plus
      hgeneric embedding)


theorem KWStraightLineCyclePhaseSign.of_alignedSideEar_five_plus
    (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneAlignedSideEar)
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCyclePhaseSign G embedding :=
  KWStraightLineCycleEarDecomposition.toPhaseSign
    (KWStraightLineCycleEarDecomposition.of_alignedSideEar_five_plus
      hgeneric embedding)


theorem KWStraightLineCyclePhaseSign.of_strictParityEar_five_plus
    (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneStrictParityEar)
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCyclePhaseSign G embedding :=
  KWStraightLineCyclePhaseSign.of_exists_removable
    (KWFiniteSimplePolygon.exists_removable_of_strictParityEar_five_plus
      hgeneric) embedding


end StatMech.FrontierA
