/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFacePositionedObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceScaleOneAudit.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFacePositionedObstruction.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem crossing_cases {x y : Site 2}
    (hx : x ∈ rect (-2) 2 (-1) 1)
    (hy : y ∈ rect (-2) 2 (-1) 1)
    (hadj : (hypercubicLattice 2).Adj x y)
    (hsplit : BottomComponentSide x ↔ ¬ BottomComponentSide y) :
    s(x, y) = s((![-2, -1] : Site 2), ![-2, 0]) ∨
      s(x, y) = s((![-1, -1] : Site 2), ![-1, 0]) ∨
      s(x, y) = s((![0, -1] : Site 2), ![0, 0]) ∨
      s(x, y) = s((![1, -1] : Site 2), ![1, 0]) ∨
      s(x, y) = s((![1, 0] : Site 2), ![2, 0]) ∨
    s(x, y) = s((![1, 1] : Site 2), ![2, 1]) := by
  rw [mem_rect] at hx hy
  have hx0Lower : -2 ≤ x 0 := hx.1
  have hx0Upper : x 0 ≤ 2 := hx.2.1
  have hx1Lower : -1 ≤ x 1 := hx.2.2.1
  have hx1Upper : x 1 ≤ 1 := hx.2.2.2
  have hxrepr : x = ![x 0, x 1] := by
    ext i
    fin_cases i <;> rfl
  rcases face_adj_dir hadj with h | h | h | h <;> subst y
  all_goals
    interval_cases hx0 : x 0 <;>
      interval_cases hx1 : x 1 <;>
      simp_all [BottomComponentSide]

theorem pims_closed_a :
    rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight
      rlc_axisReturnCounterexampleLeft
        rlc_axisReturnCounterexampleClosedConfig
      s(⟨![-2, -1], by simp [mem_rect]⟩,
        ⟨![-2, 0], by simp [mem_rect]⟩) = false := by
  rw [rlc_connectorCentralFacePIMSConfig_apply]
  have hpims : rlc_pimsEdgeEquiv
      s((![-2, -1] : Site 2), ![-2, 0]) =
        s((![1, -1] : Site 2), ![2, -1]) := by
    simpa using rlc_pimsEdgeEquiv_vertical (-2) (-1)
  rw [show (s(⟨![-2, -1], by simp [mem_rect]⟩,
      ⟨![-2, 0], by simp [mem_rect]⟩) :
      Sym2 (RlcConnectorVertex 1)).map Subtype.val =
        s((![-2, -1] : Site 2), ![-2, 0]) by rfl, hpims]
  have htrace : s((![1, -1] : Site 2), ![2, -1]) ∈
      rlc_pathEdges rlc_traceSplitCounterexampleRight.1 ∪
        rlc_pathEdges rlc_axisReturnCounterexampleLeft.1 := by
    rw [rlc_traceSplitCounterexample_right_edges]
    simp
  rw [rlc_connectorCentralFaceAmbientConfig_trace _ _ _ htrace]
  rfl

theorem pims_closed_b :
    rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight
      rlc_axisReturnCounterexampleLeft
        rlc_axisReturnCounterexampleClosedConfig
      s(⟨![-1, -1], by simp [mem_rect]⟩,
        ⟨![-1, 0], by simp [mem_rect]⟩) = false := by
  rw [rlc_connectorCentralFacePIMSConfig_apply]
  have hpims : rlc_pimsEdgeEquiv
      s((![-1, -1] : Site 2), ![-1, 0]) =
        s((![0, -1] : Site 2), ![1, -1]) := by
    simpa using rlc_pimsEdgeEquiv_vertical (-1) (-1)
  rw [show (s(⟨![-1, -1], by simp [mem_rect]⟩,
      ⟨![-1, 0], by simp [mem_rect]⟩) :
      Sym2 (RlcConnectorVertex 1)).map Subtype.val =
        s((![-1, -1] : Site 2), ![-1, 0]) by rfl, hpims]
  have htrace : s((![0, -1] : Site 2), ![1, -1]) ∈
      rlc_pathEdges rlc_traceSplitCounterexampleRight.1 ∪
        rlc_pathEdges rlc_axisReturnCounterexampleLeft.1 := by
    rw [rlc_traceSplitCounterexample_right_edges]
    simp
  rw [rlc_connectorCentralFaceAmbientConfig_trace _ _ _ htrace]
  rfl

theorem pims_closed_f :
    rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight
      rlc_axisReturnCounterexampleLeft
        rlc_axisReturnCounterexampleClosedConfig
      s(⟨![1, 1], by simp [mem_rect]⟩,
        ⟨![2, 1], by simp [mem_rect]⟩) = false := by
  rw [rlc_connectorCentralFacePIMSConfig_apply]
  have hpims : rlc_pimsEdgeEquiv
      s((![1, 1] : Site 2), ![2, 1]) =
        s((![-2, 0] : Site 2), ![-2, 1]) := by
    simpa using rlc_pimsEdgeEquiv_horizontal 1 1
  rw [show (s(⟨![1, 1], by simp [mem_rect]⟩,
      ⟨![2, 1], by simp [mem_rect]⟩) :
      Sym2 (RlcConnectorVertex 1)).map Subtype.val =
        s((![1, 1] : Site 2), ![2, 1]) by rfl, hpims]
  have htrace : s((![-2, 0] : Site 2), ![-2, 1]) ∈
      rlc_pathEdges rlc_traceSplitCounterexampleRight.1 ∪
        rlc_pathEdges rlc_axisReturnCounterexampleLeft.1 := by
    rw [rlc_axisReturnCounterexample_left_edges]
    simp
  rw [rlc_connectorCentralFaceAmbientConfig_trace _ _ _ htrace]
  rfl

theorem pims_adj_same_side {x y : RlcConnectorVertex 1}
    (hxy : (FK.openSub
      (rlc_connectorCentralFaceClosureGraph
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft)
      (rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight
        rlc_axisReturnCounterexampleLeft
          rlc_axisReturnCounterexampleClosedConfig)).Adj x y) :
    BottomComponentSide x ↔ BottomComponentSide y := by
  rw [FK.openSub_adj] at hxy
  by_contra hsame
  have hsplit : BottomComponentSide (x : Site 2) ↔
      ¬ BottomComponentSide (y : Site 2) := by
    by_cases hx : BottomComponentSide (x : Site 2) <;>
      by_cases hy : BottomComponentSide (y : Site 2) <;>
      simp_all
  obtain h | h | h | h | h | h := crossing_cases x.2 y.2 hxy.1.1 hsplit
  · have heq : s(x, y) =
        s(⟨![-2, -1], by simp [mem_rect]⟩,
          ⟨![-2, 0], by simp [mem_rect]⟩) := by
      apply Sym2.map.injective Subtype.val_injective
      simpa [Sym2.map_mk] using h
    have hopen := hxy.2
    rw [heq, pims_closed_a] at hopen
    simp at hopen
  · have heq : s(x, y) =
        s(⟨![-1, -1], by simp [mem_rect]⟩,
          ⟨![-1, 0], by simp [mem_rect]⟩) := by
      apply Sym2.map.injective Subtype.val_injective
      simpa [Sym2.map_mk] using h
    have hopen := hxy.2
    rw [heq, pims_closed_b] at hopen
    simp at hopen
  · exact bad_c_not_planar (h ▸ hxy.1.2)
  · exact bad_d_not_planar (h ▸ hxy.1.2)
  · exact bad_e_not_planar (h ▸ hxy.1.2)
  · have heq : s(x, y) =
        s(⟨![1, 1], by simp [mem_rect]⟩,
          ⟨![2, 1], by simp [mem_rect]⟩) := by
      apply Sym2.map.injective Subtype.val_injective
      simpa [Sym2.map_mk] using h
    have hopen := hxy.2
    rw [heq, pims_closed_f] at hopen
    simp at hopen

theorem pims_walk_stays_side {x y : RlcConnectorVertex 1}
    (w : (FK.openSub
      (rlc_connectorCentralFaceClosureGraph
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft)
      (rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight
        rlc_axisReturnCounterexampleLeft
          rlc_axisReturnCounterexampleClosedConfig)).Walk x y)
    (hx : BottomComponentSide x) : BottomComponentSide y := by
  induction w with
  | nil => exact hx
  | @cons u v z huv w ih =>
      exact ih ((pims_adj_same_side huv).mp hx)

theorem rlc_axisReturnCounterexample_PIMS_failure :
    rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight
        rlc_axisReturnCounterexampleLeft
          rlc_axisReturnCounterexampleClosedConfig ∉
      rlc_finiteCentralFaceClosureConnectorEvent
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
  rintro ⟨x, y, hx, hy, hxy⟩
  have hxSide : BottomComponentSide x := by
    rw [rlc_connectorOnRight,
      rlc_traceSplitCounterexample_right_vertices] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx
    all_goals
      rw [BottomComponentSide, hx]
      simp
  have hyNot : ¬ BottomComponentSide y := by
    intro hySide
    rw [rlc_connectorOnLeft,
      rlc_axisReturnCounterexample_left_vertices] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy | hy | hy
    all_goals
      rw [BottomComponentSide, hy] at hySide
      simp at hySide
  obtain ⟨w⟩ := hxy
  exact hyNot (pims_walk_stays_side w hxSide)

theorem rlc_axisReturnCounterexample_positioned_doubleFailure :
    RlcBookPositionedTracePair rlc_traceSplitCounterexampleRight
        rlc_axisReturnCounterexampleLeft ∧
      rlc_axisReturnCounterexampleClosedConfig ∉
        rlc_finiteCentralFaceRandomConnectorEvent
          rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft ∧
      rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight
          rlc_axisReturnCounterexampleLeft
            rlc_axisReturnCounterexampleClosedConfig ∉
        rlc_finiteCentralFaceClosureConnectorEvent
          rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft :=
  ⟨rlc_axisReturnCounterexample_bookPositioned,
    rlc_axisReturnCounterexample_source_failure,
    rlc_axisReturnCounterexample_PIMS_failure⟩

end
end StatMech.Universality
