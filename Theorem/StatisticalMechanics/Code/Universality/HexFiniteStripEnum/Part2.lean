/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Def.StatisticalMechanics.Code.Universality.HexFiniteStripEnum


namespace StatMech.Universality

open Complex

open HexWalk

open scoped BigOperators


theorem hexStrip_mem_verts (M : Finset ℂ) {mm : ℂ} (hmm : mm ∈ M) (hh : ℤ) :
    mm + halfStep hh ∈ hexStrip_verts M := by
  unfold hexStrip_verts
  rw [Finset.mem_biUnion]
  refine ⟨mm, hmm, ?_⟩
  rw [hexStrip_halfStep_mod6 hh]
  have h0 : 0 ≤ hh % 6 := Int.emod_nonneg hh (by norm_num)
  have h6 : hh % 6 < 6 := Int.emod_lt_of_pos hh (by norm_num)
  interval_cases (hh % 6) <;> simp


theorem hexStrip_vertexBound (M : Finset ℂ) (w : HexWalk)
    (hstay : ∀ m ∈ w.mids, m ∈ M) :
    ∀ x ∈ w.vertices, x ∈ hexStrip_verts M := by
  intro x hx
  obtain ⟨mm, hmm, hh, hxe⟩ := hexStrip_vertex_mem_eq w x hx
  rw [hxe]
  exact hexStrip_mem_verts M (hstay mm hmm) hh


end StatMech.Universality
