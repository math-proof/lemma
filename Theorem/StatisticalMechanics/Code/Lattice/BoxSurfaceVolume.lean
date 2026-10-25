/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume
open Set Finset Filter Topology


namespace StatMech

namespace Lattice

theorem boxSV_mem_boxF {d n : ℕ} {x : Site d} :
    x ∈ boxSV_boxF d n ↔ ∀ i, x i ∈ Finset.Icc (-(n : ℤ)) n := by
  unfold boxSV_boxF; rw [Fintype.mem_piFinset]


theorem boxSV_coe_boxF (d n : ℕ) : ↑(boxSV_boxF d n) = box d n := by
  ext x
  rw [Finset.mem_coe, boxSV_mem_boxF, mem_box]
  constructor
  · intro h i; have := h i; rw [Finset.mem_Icc] at this; omega
  · intro h i; rw [Finset.mem_Icc]; have := h i; omega


theorem boxSV_boxF_eq_toFinset (d n : ℕ) :
    boxSV_boxF d n = (box_finite d n).toFinset := by
  apply Finset.coe_injective
  rw [boxSV_coe_boxF, Set.Finite.coe_toFinset]


theorem boxSV_card_boxF (d n : ℕ) : (boxSV_boxF d n).card = (2 * n + 1) ^ d := by
  unfold boxSV_boxF
  rw [Fintype.card_piFinset,
    Finset.prod_congr rfl (fun i _ => by rw [Int.card_Icc])]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1; omega

theorem boxSV_boxF_subset (d : ℕ) {m n : ℕ} (h : m ≤ n) :
    boxSV_boxF d m ⊆ boxSV_boxF d n := by
  intro x hx
  rw [boxSV_mem_boxF] at *
  intro i; have := hx i; rw [Finset.mem_Icc] at *; omega


end Lattice
end StatMech
