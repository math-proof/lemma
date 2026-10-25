/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Def.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part8


namespace StatMech.Onsager

theorem ons_decMicroCorridorEdge_of_mem
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) {z : ons_DecMicroPoint L}
    (hz : z ∈ ons_decEdgeInteriorData L d e) :
    ons_decMicroCorridorEdge L z = s(d, e) := by
  change ons_decAdj L d e at hde
  rcases hde with hrev | hint
  · subst e
    rcases d with ⟨p, mu⟩
    fin_cases mu <;>
      simp [ons_decEdgeInteriorData] at hz <;>
      rcases hz with rfl | rfl | rfl <;>
      simp [ons_decMicroCorridorEdge, ons_dartRev, ons_dirStep,
        Sym2.eq_iff] <;> ring
  · rcases d with ⟨p, mu⟩
    rcases e with ⟨q, nu⟩
    have hpq : p = q := hint.1
    subst q
    have hnotrev : (p, nu) ≠ ons_dartRev L (p, mu) := by
      intro h
      have hs := congrArg (fun d : ons_Dart L => d.1) h
      exact ons_dirStep_ne_self L mu p hs.symm
    unfold ons_decEdgeInteriorData at hz
    rw [if_neg hnotrev] at hz
    fin_cases mu <;> fin_cases nu
    all_goals simp [ons_decInternalAdj] at hint
    all_goals simp at hz
    all_goals
      rcases hz with rfl | rfl | rfl <;>
      simp [ons_decMicroCorridorEdge, Sym2.eq_iff]

@[simp] theorem ons_decEdgeRoute_interior_support
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    (ons_decEdgeRoute L d e hde).support.tail.dropLast =
      (ons_decEdgeInteriorData L d e).map (ons_decMicroVertex L) := by
  rw [ons_decEdgeRoute_support]
  change ons_decAdj L d e at hde
  rcases hde with hrev | hint
  · subst e
    rcases d with ⟨⟨x, y⟩, mu⟩
    fin_cases mu <;>
      simp [ons_decEdgeRouteVertices, ons_decEdgeRouteDirs,
        ons_decEdgeInteriorData, ons_decMicroVertex, ons_decEmbedVertex,
        ons_decEmbedOffset, ons_dartRev, ons_dirStep]
    all_goals
      repeat' apply And.intro
      all_goals first
      | simpa [add_comm, mul_comm] using ons_eight_zmodCast_add_one L x
      | simpa [add_comm, mul_comm] using ons_eight_zmodCast_add_one L y
      | have hs := ons_eight_zmodCast_sub_one L x
        simp [sub_eq_add_neg, add_comm, mul_comm] at hs ⊢
        linear_combination hs
      | have hs := ons_eight_zmodCast_sub_one L y
        simp [sub_eq_add_neg, add_comm, mul_comm] at hs ⊢
        linear_combination hs
      | linear_combination ons_eight_zmodCast_add_one L x
      | linear_combination ons_eight_zmodCast_add_one L y
      | linear_combination ons_eight_zmodCast_sub_one L x
      | linear_combination ons_eight_zmodCast_sub_one L y
      | ring
  · exact ons_decInternalRoute_interior_support L d e hint


theorem ons_decEdgeRoute_edge_eq_of_interior_mem
    (L : ℕ) [Fact (2 < L)]
    (d e f g : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e)
    (hfg : (ons_decGraph L).Adj f g)
    {x : ZMod (8 * L) × ZMod (8 * L)}
    (hx : x ∈ (ons_decEdgeRoute L d e hde).support.tail.dropLast)
    (hy : x ∈ (ons_decEdgeRoute L f g hfg).support.tail.dropLast) :
    s(d, e) = s(f, g) := by
  rw [ons_decEdgeRoute_interior_support] at hx hy
  rcases List.mem_map.mp hx with ⟨z, hz, hzx⟩
  rcases List.mem_map.mp hy with ⟨w, hw, hwx⟩
  have hzw : z = w := ons_decMicroVertex_injective L (hzx.trans hwx.symm)
  calc
    s(d, e) = ons_decMicroCorridorEdge L z :=
      (ons_decMicroCorridorEdge_of_mem L d e hde hz).symm
    _ = ons_decMicroCorridorEdge L w := by rw [hzw]
    _ = s(f, g) := ons_decMicroCorridorEdge_of_mem L f g hfg hw

end StatMech.Onsager
