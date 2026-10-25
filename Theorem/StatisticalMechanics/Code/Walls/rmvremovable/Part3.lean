/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.atcattachstep.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc_leafremoval.Part2
import Theorem.StatisticalMechanics.Code.Walls.nbcnoncut.Part2
import Theorem.StatisticalMechanics.Code.Walls.earremovable.Part5
import Def.StatisticalMechanics.Code.Walls.rmvremovable.Part2
open Finset Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem rmv_removable_of_extreme_ne_origin (hres : rmv_ReflexCornerResidue)
    {K : Finset (Site 2)} (hcard : 2 ≤ K.card) (hconn : IsConnectedCluster K) {c : Site 2}
    (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c) (hcorigin : c ≠ origin 2) :
    ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
      CellConnected ((↑K : Set (Site 2)) \ {d}) := by
  rcases rmv_extreme_dichotomy hcard hconn hc hcorigin with hrem | ⟨hp, hq, hdiag⟩
  · exact hrem
  · exact hres K hcard hconn c hc hcorigin hp hq hdiag


theorem rmv_nbc_of_reflexResidue (hres : rmv_ReflexCornerResidue)
    (hresAnti : rmv_AntiReflexCornerResidue) : nbc_BoundaryNonCutExists := by
  classical
  intro K hcard hconn
  
  obtain ⟨c, hc⟩ := ear_exists_globalExtreme (↑K : Set (Site 2)) K.finite_toSet
    (by rw [Finset.coe_nonempty]; exact ⟨origin 2, hconn.1⟩)
  by_cases hco : c = origin 2
  · 
    obtain ⟨b, hb⟩ := ear_exists_antiExtreme (↑K : Set (Site 2)) K.finite_toSet
      (by rw [Finset.coe_nonempty]; exact ⟨origin 2, hconn.1⟩)
    have hbc : b ≠ c := (ear_extremes_distinct hcard hc hb).symm
    have hborigin : b ≠ origin 2 := by rw [hco] at hbc; exact hbc
    
    rcases ear_antiExtreme_dichotomy hcard hconn hb hborigin with hrem | ⟨hr, hu⟩
    · exact hrem
    · 
      by_cases hdiag : b + ![1, 1] ∈ (↑K : Set (Site 2))
      · 
        refine ⟨b, by exact_mod_cast hb.mem, hborigin,
          ear_antiExtreme_boundary (↑K : Set (Site 2)) b hb, ?_⟩
        refine rmv_noncut_of_common_neighbour
          (nbc_cellConnected_of_isConnectedCluster hconn) hb.mem hdiag ?_ ?_
        · intro h; have := congrFun h 0; simp [Pi.add_apply] at this
        · intro z hzK hadj _
          rcases ear_antiExtreme_neighbor_rightCell_or_upCell (↑K : Set (Site 2)) b z hb hzK hadj
            with h | h
          · rw [h, ear_rightCell]
            rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp only [Pi.add_apply]; norm_num
          · rw [h, ear_upCell]
            rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp only [Pi.add_apply]; norm_num
      · 
        exact hresAnti K hcard hconn b hb hborigin hr hu hdiag
  · 
    exact rmv_removable_of_extreme_ne_origin hres hcard hconn hc hco


theorem rmv_atc_of_reflexResidue (hres : rmv_ReflexCornerResidue)
    (hresAnti : rmv_AntiReflexCornerResidue) : atc_HasRemovableConnCell :=
  nbc_atc_of_boundaryNonCut (rmv_nbc_of_reflexResidue hres hresAnti)


theorem rmv_fbc_hasRemovableCell_of_reflexResidue (hres : rmv_ReflexCornerResidue)
    (hresAnti : rmv_AntiReflexCornerResidue) : fbc_HasRemovableCell :=
  nbc_fbc_hasRemovableCell_of_boundaryNonCut (rmv_nbc_of_reflexResidue hres hresAnti)

end Walls
end StatMech
