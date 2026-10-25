/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part38
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


@[simp] theorem fkRectStripTorusRowEquiv_val
    (R : FKRectTorus) (i : Fin (R.height - 1 + 1)) :
    (fkRectStripTorusRowEquiv R i).val = i.val := rfl

@[simp] theorem fkRectStripTorusRowEquiv_succ
    (R : FKRectTorus) (i : Fin (R.height - 1)) :
    fkRectStripTorusRowEquiv R i.succ =
      fkRectBoundaryNonSeamRow R i := rfl

@[simp] theorem fkRectStripTorusRowEquiv_zero (R : FKRectTorus) :
    fkRectStripTorusRowEquiv R (0 : Fin (R.height - 1 + 1)) =
      fkRectBoundarySeamRow R := rfl

theorem fkRect_cyclicPred_nonSeamRow
    (R : FKRectTorus) (i : Fin (R.height - 1)) :
    SixVertexArrows.cyclicPred R.height_pos
        (fkRectBoundaryNonSeamRow R i) =
      fkRectStripTorusRowEquiv R i.castSucc := by
  ext
  simp only [SixVertexArrows.cyclicPred,
    fkRectBoundaryNonSeamRow_val, Fin.val_mk,
    fkRectStripTorusRowEquiv_val, Fin.val_castSucc]
  rw [show i.val + 1 + R.height - 1 = R.height + i.val by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt]
  exact i.isLt.trans_le (Nat.sub_le _ _)

theorem fkRect_cyclicPred_seamRow (R : FKRectTorus) :
    SixVertexArrows.cyclicPred R.height_pos
        (fkRectBoundarySeamRow R) =
      fkRectStripTorusRowEquiv R (Fin.last (R.height - 1)) := by
  ext
  simp only [SixVertexArrows.cyclicPred, fkRectBoundarySeamRow,
    Fin.val_mk, zero_add, fkRectStripTorusRowEquiv_val, Fin.val_last]
  rw [Nat.mod_eq_of_lt]
  all_goals have hp := R.height_pos; omega

theorem fkRectCoordinateLayerEdge_map_eq_indexedEdge
    (R : FKRectTorus) (i : Fin (R.height - 1))
    (a : Bool × Fin R.width) :
    Sym2.map (fkRectStripCoordinateTorusEquiv R)
        (fkRectCoordinateLayerEdge R.width_pos i
          (decide (Even (fkRectBoundaryNonSeamRow R i).val)) a) =
      fkRectTorusIndexedEdge R
        (a.1, (a.2, fkRectBoundaryNonSeamRow R i)) := by
  rcases a with ⟨dir, x⟩
  cases dir
  · by_cases he : Even (fkRectBoundaryNonSeamRow R i).val
    · have he' : Even (i.val + 1) := by simpa using he
      simp [fkRectCoordinateLayerEdge,
        fkRectCoordinateLayerEdgeEndpoints,
        fkRectStripCoordinateTorusEquiv, fkRectTorusIndexedEdge, he',
        fkRect_cyclicPred_nonSeamRow, Sym2.eq_swap]
    · have he' : ¬Even (i.val + 1) := by simpa using he
      simp [fkRectCoordinateLayerEdge,
        fkRectCoordinateLayerEdgeEndpoints,
        fkRectStripCoordinateTorusEquiv, fkRectTorusIndexedEdge, he',
        fkRect_cyclicPred_nonSeamRow, Sym2.eq_swap]
  · simp [fkRectCoordinateLayerEdge,
      fkRectCoordinateLayerEdgeEndpoints,
      fkRectStripCoordinateTorusEquiv, fkRectTorusIndexedEdge,
      fkRect_cyclicPred_nonSeamRow, Sym2.eq_swap]

theorem fkRectCoordinateSeamEdge_map_eq_indexedEdge
    (R : FKRectTorus) (a : Bool × Fin R.width) :
    Sym2.map (fkRectStripCoordinateTorusEquiv R)
        (fkRectCoordinateSeamEdge (n := R.height - 1) R.width_pos a) =
      fkRectTorusIndexedEdge R
        (a.1, (a.2, fkRectBoundarySeamRow R)) := by
  rcases a with ⟨dir, x⟩
  have he : Even (fkRectBoundarySeamRow R).val := by
    simp [fkRectBoundarySeamRow]
  cases dir
  · simp [fkRectCoordinateSeamEdge,
      fkRectStripCoordinateTorusEquiv, fkRectTorusIndexedEdge,
      fkRect_cyclicPred_seamRow, he, Sym2.eq_swap]
  · simp [fkRectCoordinateSeamEdge,
      fkRectStripCoordinateTorusEquiv, fkRectTorusIndexedEdge,
      fkRect_cyclicPred_seamRow, he, Sym2.eq_swap]

theorem fkRectOpenGraph_adj_iff_coordinateSchedule
    (R : FKRectTorus) (omega : R.Configuration)
    (u v : Fin R.width × Fin (R.height - 1 + 1)) :
    (fkRectOpenGraph R omega).Adj
        (fkRectStripCoordinateTorusEquiv R u)
        (fkRectStripCoordinateTorusEquiv R v) ↔
      u ≠ v ∧
        ((∃ i : Fin (R.height - 1), ∃ a : Bool × Fin R.width,
          (fkRectConfigurationNonSeamLayerFn R omega i).2 a = true ∧
            fkRectCoordinateLayerEdge R.width_pos i
                (fkRectConfigurationNonSeamLayerFn R omega i).1 a =
              s(u, v)) ∨
        ∃ a : Bool × Fin R.width,
          fkRectConfigurationLayer R omega (fkRectBoundarySeamRow R) a =
              true ∧
            fkRectCoordinateSeamEdge (n := R.height - 1)
                R.width_pos a = s(u, v)) := by
  constructor
  · intro hadj
    have hne : u ≠ v := by
      intro huv
      subst v
      exact (fkRectOpenGraph R omega).loopless.irrefl _ hadj
    refine ⟨hne, ?_⟩
    obtain ⟨⟨dir, ⟨x, y⟩⟩, hopen, hedge⟩ := hadj
    by_cases hy : y.val = 0
    · have hy' : y = fkRectBoundarySeamRow R := Fin.ext hy
      subst y
      refine Or.inr ⟨(dir, x), hopen, ?_⟩
      apply (sym2_map_eq_map_iff_of_injective
        (fkRectStripCoordinateTorusEquiv R)
        (fkRectStripCoordinateTorusEquiv R).injective _ _).1
      rw [fkRectCoordinateSeamEdge_map_eq_indexedEdge]
      simpa only [Sym2.map_pair_eq] using hedge
    · let i : Fin (R.height - 1) :=
        ⟨y.val - 1, by
          have hylt := y.isLt
          have hp := R.height_pos
          omega⟩
      have hy' : y = fkRectBoundaryNonSeamRow R i := by
        apply Fin.ext
        simp only [fkRectBoundaryNonSeamRow_val]
        dsimp only [i]
        omega
      rw [hy'] at hopen hedge
      refine Or.inl ⟨i, (dir, x), hopen, ?_⟩
      change fkRectCoordinateLayerEdge R.width_pos i
        (decide (Even (fkRectBoundaryNonSeamRow R i).val)) (dir, x) =
          s(u, v)
      apply (sym2_map_eq_map_iff_of_injective
        (fkRectStripCoordinateTorusEquiv R)
        (fkRectStripCoordinateTorusEquiv R).injective _ _).1
      rw [fkRectCoordinateLayerEdge_map_eq_indexedEdge]
      simpa only [Sym2.map_pair_eq] using hedge
  · rintro ⟨_, hnonSeam | hseam⟩
    · obtain ⟨i, a, hopen, hcoord⟩ := hnonSeam
      refine ⟨(a.1, (a.2, fkRectBoundaryNonSeamRow R i)), hopen, ?_⟩
      change fkRectCoordinateLayerEdge R.width_pos i
        (decide (Even (fkRectBoundaryNonSeamRow R i).val)) a = s(u, v)
        at hcoord
      rw [← fkRectCoordinateLayerEdge_map_eq_indexedEdge]
      rw [hcoord, Sym2.map_pair_eq]
    · obtain ⟨a, hopen, hcoord⟩ := hseam
      refine ⟨(a.1, (a.2, fkRectBoundarySeamRow R)), hopen, ?_⟩
      rw [← fkRectCoordinateSeamEdge_map_eq_indexedEdge]
      rw [hcoord, Sym2.map_pair_eq]


end
end StatMech.FrontierD
