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
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part6


namespace StatMech.FrontierA

noncomputable def KWStraightLineEmbedding.cyclePolygon
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    KWFiniteSimplePolygon p.darts.length := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let loop := kwGraphCycleDartLoop p
  have hvalid := kwGraphCycleDartLoop_valid p hp
  have hedgeNodup :
      (List.ofFn fun i : Fin p.darts.length ↦ (loop i).edge).Nodup := by
    rw [List.ofFn_comp', kwGraphCycleDartLoop_ofFn]
    simpa [SimpleGraph.Walk.edges] using hp.edges_nodup
  have hedgeInj : Function.Injective
      (fun i : Fin p.darts.length ↦ (loop i).edge) :=
    List.nodup_ofFn.mp hedgeNodup
  have hloopFst : ∀ i : Fin p.darts.length,
      (loop i).fst = p.getVert i.val := by
    intro i
    exact congrArg (fun dart : G.Dart ↦ dart.fst)
      (SimpleGraph.Walk.darts_getElem_eq_getVert i.val i.isLt)
  have hloopFstInj : Function.Injective
      (fun i : Fin p.darts.length ↦ (loop i).fst) := by
    intro i j hij
    apply Fin.ext
    apply hp.getVert_injOn'
    · simp only [Set.mem_setOf_eq]
      rw [← SimpleGraph.Walk.length_darts]
      exact Nat.le_sub_one_of_lt i.isLt
    · simp only [Set.mem_setOf_eq]
      rw [← SimpleGraph.Walk.length_darts]
      exact Nat.le_sub_one_of_lt j.isLt
    · simpa only [hloopFst i, hloopFst j] using hij
  refine
    { vertex := fun i ↦ embedding.vertex (loop i).fst
      three_le := by
        rw [SimpleGraph.Walk.length_darts]
        exact hp.three_le_length
      vertex_injective := ?_
      vertex_not_strictly_between := ?_
      edgeInteriors_disjoint := ?_ }
  · intro i j hij
    exact hloopFstInj (embedding.vertex_injective hij)
  · intro i j hji hjsucc
    have hjfst : (loop j).fst ≠ (loop i).fst :=
      hloopFstInj.ne hji
    have hjsnd : (loop j).fst ≠ (loop i).snd := by
      rw [hvalid i]
      exact hloopFstInj.ne hjsucc
    change ¬Sbtw ℝ (embedding.vertex (loop i).fst)
      (embedding.vertex (loop j).fst) (embedding.vertex (loop (i + 1)).fst)
    rw [← hvalid i]
    exact embedding.vertex_not_strictly_between (loop i) (loop j).fst
      hjfst hjsnd
  · intro i j hij
    change Disjoint
      {z : ℂ | Sbtw ℝ (embedding.vertex (loop i).fst) z
        (embedding.vertex (loop (i + 1)).fst)}
      {z : ℂ | Sbtw ℝ (embedding.vertex (loop j).fst) z
        (embedding.vertex (loop (j + 1)).fst)}
    rw [← hvalid i, ← hvalid j]
    exact embedding.edgeInteriors_disjoint (loop i) (loop j)
      (fun hedge ↦ hij (hedgeInj hedge))


end StatMech.FrontierA
