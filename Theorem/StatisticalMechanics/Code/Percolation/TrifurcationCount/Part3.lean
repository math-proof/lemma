/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMergeGeom
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Def.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem tfc_boundaryFinset_card (d n : ℕ) :
    (tfc_boundaryFinset d n).card = boxSV_boundaryCard d n := rfl

theorem tfc_mem_trifFinset {ω : ConfigSpace (Sym2 (Site d))} {n : ℕ} {x : Site d} :
    x ∈ tfc_trifFinset ω n ↔ x ∈ box d n ∧ IsTrifurcation d ω x := by
  classical
  rw [tfc_trifFinset, Finset.mem_filter, boxFinsetBK, Set.Finite.mem_toFinset]

theorem tfc_mem_boundaryFinset {d n : ℕ} {x : Site d} :
    x ∈ tfc_boundaryFinset d n ↔ x ∈ vertexBoundary d n := by
  rw [tfc_boundaryFinset, Set.Finite.mem_toFinset]


theorem tfc_boundaryCard_zero (d : ℕ) : boxSV_boundaryCard d 0 = 0 := by
  unfold boxSV_boundaryCard
  rw [Set.Finite.toFinset_eq_empty.mpr, Finset.card_empty]
  rw [vertexBoundary]; norm_num


theorem tfc_Tcount_le_of_injOn (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (φ : Site d → Site d)
    (hmaps : ∀ x, x ∈ box d n → IsTrifurcation d ω x → φ x ∈ vertexBoundary d n)
    (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → φ x = φ y → x = y) :
    Tcount d ω n ≤ boxSV_boundaryCard d n := by
  classical
  rw [← tfc_trifFinset_card, ← tfc_boundaryFinset_card]
  refine Finset.card_le_card_of_injOn φ ?_ ?_
  · intro x hx
    rw [Finset.mem_coe, tfc_mem_trifFinset] at hx
    rw [Finset.mem_coe, tfc_mem_boundaryFinset]
    exact hmaps x hx.1 hx.2
  · intro x hx y hy hxy
    rw [Finset.mem_coe, tfc_mem_trifFinset] at hx hy
    exact hinj x hx.1 hx.2 y hy.1 hy.2 hxy


theorem tfc_Tcount_le_card (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (φ : Site d → Site d)
    (hmaps : Set.MapsTo φ (tfc_trifFinset ω n) (tfc_boundaryFinset d n))
    (hinj : Set.InjOn φ (tfc_trifFinset ω n)) :
    Tcount d ω n ≤ boxSV_boundaryCard d n := by
  rw [← tfc_trifFinset_card, ← tfc_boundaryFinset_card]
  exact Finset.card_le_card_of_injOn φ hmaps hinj


end Percolation
end StatMech
