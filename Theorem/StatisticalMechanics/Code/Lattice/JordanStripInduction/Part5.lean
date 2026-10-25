/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ArcSides.Part3
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
import Def.StatisticalMechanics.Code.Lattice.JordanStripInduction.Part3
open Set SimpleGraph MeasureTheory


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


@[simp] theorem jsi_mem_leftRegionLt (col : ℤ → ℤ) (α β c d : ℤ) (z : Site 2) :
    z ∈ jsi_leftRegionLt col α β c d ↔ z ∈ rect α β c d ∧ z 0 < col (z 1) := Iff.rfl


theorem jsi_arcSeparatingSet {P : Set (Site 2)} {α β m m' c d : ℤ}
    (hαm : α ≤ m) (hm'β : m' < β) (A : JsiRowArc P m m' c d) :
    ArcSeparatingSet P α β c d := by
  classical
  refine ⟨jsi_leftRegion A.col α β c d, ?_, ?_, ?_⟩
  · 
    intro z hz hzα
    refine ⟨hz, ?_⟩
    rw [hzα]
    have hzrow := mem_rect.mp hz
    exact le_trans hαm (A.band_lo (z 1) hzrow.2.2.1 hzrow.2.2.2)
  · 
    intro z hz hzβ
    rw [jsi_mem_leftRegion]
    push Not
    intro _
    rw [hzβ]
    have hzrow := mem_rect.mp hz
    have hb : A.col (z 1) ≤ m' := A.band_hi (z 1) hzrow.2.2.1 hzrow.2.2.2
    omega
  · 
    intro u v hu hv hadj hbd
    rw [bdEdge_mk] at hbd
    have hurow := mem_rect.mp hu
    have hvrow := mem_rect.mp hv
    by_cases huS : u ∈ jsi_leftRegion A.col α β c d
    · 
      have hvS : v ∉ jsi_leftRegion A.col α β c d := hbd.mp huS
      have hu_le : u 0 ≤ A.col (u 1) := huS.2
      have hv_gt : A.col (v 1) < v 0 := by
        by_contra h; push Not at h; exact hvS ⟨hv, h⟩
      rcases jsi_adj_cases u v hadj with ⟨hrow, _⟩ | ⟨hcoleq, hrowdiff⟩
      · 
        left
        have hcr : u 0 = A.col (u 1) := by
          have hadj' := hypercubicLattice_adj 2 u v
          rw [hadj', Fin.sum_univ_two] at hadj
          rw [← hrow] at hv_gt; omega
        exact A.on_arc u hurow.2.2.1 hurow.2.2.2 hcr
          (le_trans (A.band_lo (u 1) hurow.2.2.1 hurow.2.2.2) (le_of_eq hcr.symm))
          (hcr ▸ A.band_hi (u 1) hurow.2.2.1 hurow.2.2.2)
      · 
        left
        have hcc := jsi_col_consecutive A (u 1) (v 1) hurow.2.2.1 hurow.2.2.2
          hvrow.2.2.1 hvrow.2.2.2 hrowdiff
        rw [← hcoleq] at hv_gt
        have hcr : u 0 = A.col (u 1) := by omega
        exact A.on_arc u hurow.2.2.1 hurow.2.2.2 hcr
          (le_trans (A.band_lo (u 1) hurow.2.2.1 hurow.2.2.2) (le_of_eq hcr.symm))
          (hcr ▸ A.band_hi (u 1) hurow.2.2.1 hurow.2.2.2)
    · 
      have hvS : v ∈ jsi_leftRegion A.col α β c d := by
        by_contra h; exact huS (hbd.mpr h)
      have hv_le : v 0 ≤ A.col (v 1) := hvS.2
      have hu_gt : A.col (u 1) < u 0 := by
        by_contra h; push Not at h; exact huS ⟨hu, h⟩
      rcases jsi_adj_cases u v hadj with ⟨hrow, _⟩ | ⟨hcoleq, hrowdiff⟩
      · 
        right
        have hcr : v 0 = A.col (v 1) := by
          rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
          rw [hrow] at hu_gt; omega
        exact A.on_arc v hvrow.2.2.1 hvrow.2.2.2 hcr
          (le_trans (A.band_lo (v 1) hvrow.2.2.1 hvrow.2.2.2) (le_of_eq hcr.symm))
          (hcr ▸ A.band_hi (v 1) hvrow.2.2.1 hvrow.2.2.2)
      · 
        right
        have hcc := jsi_col_consecutive A (v 1) (u 1) hvrow.2.2.1 hvrow.2.2.2
          hurow.2.2.1 hurow.2.2.2 (by omega)
        rw [hcoleq] at hu_gt
        have hcr : v 0 = A.col (v 1) := by omega
        exact A.on_arc v hvrow.2.2.1 hvrow.2.2.2 hcr
          (le_trans (A.band_lo (v 1) hvrow.2.2.1 hvrow.2.2.2) (le_of_eq hcr.symm))
          (hcr ▸ A.band_hi (v 1) hvrow.2.2.1 hvrow.2.2.2)


theorem jsi_arcSeparatingSetLt {P : Set (Site 2)} {α β m m' c d : ℤ}
    (hαm : α < m) (hm'β : m' ≤ β) (A : JsiRowArc P m m' c d) :
    ArcSeparatingSet P α β c d := by
  classical
  refine ⟨jsi_leftRegionLt A.col α β c d, ?_, ?_, ?_⟩
  · 
    intro z hz hzα
    refine ⟨hz, ?_⟩
    rw [hzα]
    have hzrow := mem_rect.mp hz
    exact lt_of_lt_of_le hαm (A.band_lo (z 1) hzrow.2.2.1 hzrow.2.2.2)
  · 
    intro z hz hzβ
    rw [jsi_mem_leftRegionLt]
    push Not
    intro _
    rw [hzβ]
    have hzrow := mem_rect.mp hz
    have hb : A.col (z 1) ≤ m' := A.band_hi (z 1) hzrow.2.2.1 hzrow.2.2.2
    omega
  · 
    intro u v hu hv hadj hbd
    rw [bdEdge_mk] at hbd
    have hurow := mem_rect.mp hu
    have hvrow := mem_rect.mp hv
    by_cases huS : u ∈ jsi_leftRegionLt A.col α β c d
    · 
      have hvS : v ∉ jsi_leftRegionLt A.col α β c d := hbd.mp huS
      have hu_lt : u 0 < A.col (u 1) := huS.2
      have hv_ge : A.col (v 1) ≤ v 0 := by
        by_contra h; push Not at h; exact hvS ⟨hv, h⟩
      rcases jsi_adj_cases u v hadj with ⟨hrow, _⟩ | ⟨hcoleq, hrowdiff⟩
      · 
        right
        have hce : A.col (u 1) = A.col (v 1) := by rw [hrow]
        have hcr : v 0 = A.col (v 1) := by
          rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
          omega
        exact A.on_arc v hvrow.2.2.1 hvrow.2.2.2 hcr
          (le_trans (A.band_lo (v 1) hvrow.2.2.1 hvrow.2.2.2) (le_of_eq hcr.symm))
          (hcr ▸ A.band_hi (v 1) hvrow.2.2.1 hvrow.2.2.2)
      · 
        right
        have hcc := jsi_col_consecutive A (v 1) (u 1) hvrow.2.2.1 hvrow.2.2.2
          hurow.2.2.1 hurow.2.2.2 (by omega)
        rw [hcoleq] at hu_lt
        have hcr : v 0 = A.col (v 1) := by omega
        exact A.on_arc v hvrow.2.2.1 hvrow.2.2.2 hcr
          (le_trans (A.band_lo (v 1) hvrow.2.2.1 hvrow.2.2.2) (le_of_eq hcr.symm))
          (hcr ▸ A.band_hi (v 1) hvrow.2.2.1 hvrow.2.2.2)
    · 
      have hvS : v ∈ jsi_leftRegionLt A.col α β c d := by
        by_contra h; exact huS (hbd.mpr h)
      have hv_lt : v 0 < A.col (v 1) := hvS.2
      have hu_ge : A.col (u 1) ≤ u 0 := by
        by_contra h; push Not at h; exact huS ⟨hu, h⟩
      rcases jsi_adj_cases u v hadj with ⟨hrow, _⟩ | ⟨hcoleq, hrowdiff⟩
      · 
        left
        have hce : A.col (u 1) = A.col (v 1) := by rw [hrow]
        have hcr : u 0 = A.col (u 1) := by
          rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
          omega
        exact A.on_arc u hurow.2.2.1 hurow.2.2.2 hcr
          (le_trans (A.band_lo (u 1) hurow.2.2.1 hurow.2.2.2) (le_of_eq hcr.symm))
          (hcr ▸ A.band_hi (u 1) hurow.2.2.1 hurow.2.2.2)
      · 
        left
        have hcc := jsi_col_consecutive A (u 1) (v 1) hurow.2.2.1 hurow.2.2.2
          hvrow.2.2.1 hvrow.2.2.2 hrowdiff
        rw [← hcoleq] at hv_lt
        have hcr : u 0 = A.col (u 1) := by omega
        exact A.on_arc u hurow.2.2.1 hurow.2.2.2 hcr
          (le_trans (A.band_lo (u 1) hurow.2.2.1 hurow.2.2.2) (le_of_eq hcr.symm))
          (hcr ▸ A.band_hi (u 1) hurow.2.2.1 hurow.2.2.2)


end Lattice
end StatMech
