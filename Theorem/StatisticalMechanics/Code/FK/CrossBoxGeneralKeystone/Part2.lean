/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxReduce.Part2
import Theorem.StatisticalMechanics.Code.FK.DisjointGraphFactorizeClose.Part2
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Theorem.StatisticalMechanics.Code.FK.MultiEdgeDecay.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Def.StatisticalMechanics.Code.FK.CrossBoxGeneralKeystone
open MeasureTheory Filter Topology Set SimpleGraph
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}


theorem cbk_vrad_shiftVec {d : ℕ} (i₀ : Fin d) (N : ℕ) :
    flc_vrad (cbk_shiftVec i₀ N) = 2 * N + 1 := by
  have habs : ((2 * (N : ℤ) + 1)).natAbs = 2 * N + 1 := by
    rw [Int.natAbs_eq_iff]; left; push_cast; ring
  unfold flc_vrad cbk_shiftVec
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    by_cases hi : i = i₀ <;> simp only [hi, if_true, if_false]
    · rw [habs]
    · simp
  · refine le_trans ?_ (Finset.le_sup
      (f := fun i => ((if i = i₀ then (2 * (N : ℤ) + 1) else 0)).natAbs) (Finset.mem_univ i₀))
    simp only [if_true]
    rw [habs]


theorem cbk_box_disjoint_transBox {d : ℕ} (i₀ : Fin d) (N : ℕ) {y : Site d}
    (hy : y ∈ box d N) (hyt : y ∈ fvs_transBox d N (cbk_shiftVec i₀ N)) : False := by
  have h0 : (y i₀).natAbs ≤ N := hy i₀
  have hyt' : (y - cbk_shiftVec i₀ N) ∈ box d N := hyt
  have h1 : ((y - cbk_shiftVec i₀ N) i₀).natAbs ≤ N := hyt' i₀
  have hv0 : cbk_shiftVec i₀ N i₀ = (2 * N + 1 : ℤ) := by simp [cbk_shiftVec]
  have hsub : (y - cbk_shiftVec i₀ N) i₀ = y i₀ - (2 * N + 1 : ℤ) := by
    simp [Pi.sub_apply, hv0]
  rw [hsub] at h1
  have ha : |y i₀| ≤ (N : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h0
  have hb : |y i₀ - (2 * N + 1 : ℤ)| ≤ (N : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast h1
  rw [abs_le] at ha hb
  omega


end FK
end StatMech
