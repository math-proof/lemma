/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanInclusionExclusion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Def.StatisticalMechanics.Code.Ising.AizenmanInclusionExclusion
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


theorem aie_noneConn_not_allConn (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (h : aie_noneConn ends m o x y) : ¬ aie_allConn ends m o x y := by
  rintro ⟨h1, _, _⟩; exact h.1 h1


theorem aie_backbone_trichotomy (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) :
    asd_ghsBackboneFactor ends m o x y = 1
    ∨ asd_ghsBackboneFactor ends m o x y = 0
    ∨ asd_ghsBackboneFactor ends m o x y = -2 := by
  unfold asd_ghsBackboneFactor
  by_cases hxy : connK ends m x y <;> by_cases hoy : connK ends m o y <;>
    by_cases hox : connK ends m o x
  · right; right; rw [if_pos hxy, if_pos hoy, if_pos hox]; norm_num
  · exact absurd (aie_conn_trans_ox ends m hxy hoy) hox
  · exact absurd (aie_conn_trans_oy ends m hxy hox) hoy
  · right; left; rw [if_pos hxy, if_neg hoy, if_neg hox]; norm_num
  · exact absurd (aie_conn_trans_xy ends m hoy hox) hxy
  · right; left; rw [if_neg hxy, if_pos hoy, if_neg hox]; norm_num
  · right; left; rw [if_neg hxy, if_neg hoy, if_pos hox]; norm_num
  · left; rw [if_neg hxy, if_neg hoy, if_neg hox]; norm_num


theorem aie_backbone_value_none (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (h : aie_noneConn ends m o x y) : asd_ghsBackboneFactor ends m o x y = 1 :=
  asd_ghsBackboneFactor_noConn ends m h.1 h.2.1 h.2.2


theorem aie_backbone_value_all (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (h : aie_allConn ends m o x y) : asd_ghsBackboneFactor ends m o x y = -2 :=
  asd_ghsBackboneFactor_allConn ends m h.1 h.2.1 h.2.2


theorem aie_backbone_value_one (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hnotall : ¬ aie_allConn ends m o x y) (hnotnone : ¬ aie_noneConn ends m o x y) :
    asd_ghsBackboneFactor ends m o x y = 0 := by
  unfold asd_ghsBackboneFactor
  simp only [aie_allConn, aie_noneConn] at hnotall hnotnone
  by_cases hxy : connK ends m x y <;> by_cases hoy : connK ends m o y <;>
    by_cases hox : connK ends m o x
  · exact absurd ⟨hxy, hoy, hox⟩ hnotall
  · exact absurd (aie_conn_trans_ox ends m hxy hoy) hox
  · exact absurd (aie_conn_trans_oy ends m hxy hox) hoy
  · rw [if_pos hxy, if_neg hoy, if_neg hox]; norm_num
  · exact absurd (aie_conn_trans_xy ends m hoy hox) hxy
  · rw [if_neg hxy, if_pos hoy, if_neg hox]; norm_num
  · rw [if_neg hxy, if_neg hoy, if_pos hox]; norm_num
  · exact absurd ⟨hxy, hoy, hox⟩ hnotnone


theorem aie_backbone_factor_nonneg_not_all (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hnotall : ¬ aie_allConn ends m o x y) : 0 ≤ asd_ghsBackboneFactor ends m o x y := by
  by_cases hnone : aie_noneConn ends m o x y
  · rw [aie_backbone_value_none ends m hnone]; norm_num
  · rw [aie_backbone_value_one ends m hnotall hnone]


end RandomCurrent
end Sharpness
end StatMech
