/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
import Def.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part7
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jcb_diagK_not_kingSat : ¬ npm_KingSaturated jcb_diagK := by
  intro h
  have hc := (h ![0, 0]).1
  simp only [npd_P00, npd_P11, npd_P10, npd_P01,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hc
  have h00 : (![(0:ℤ), 0] : Site 2) ∈ jcb_diagK := Or.inl rfl
  have h11 : (![(0:ℤ) + 1, 0 + 1] : Site 2) ∈ jcb_diagK := by
    right; rw [Set.mem_singleton_iff, site2_eq]; norm_num
  rcases hc h00 h11 with h10 | h01
  · rw [jcb_diagK, Set.mem_insert_iff, Set.mem_singleton_iff, site2_eq, site2_eq] at h10; omega
  · rw [jcb_diagK, Set.mem_insert_iff, Set.mem_singleton_iff, site2_eq, site2_eq] at h01; omega


theorem jcb_diagK_not_own_starHull : ndt_StarHull jcb_diagK ≠ jcb_diagK := by
  intro heq
  exact jcb_diagK_not_kingSat (heq ▸ ndt_kingSaturated_starHull jcb_diagK)


theorem jcb_status :
    (∀ P : PlanarZ2Subgraph, Nat.card (jcb_BoundedRegion P) = nullity P.G) ∧
    (∀ P : PlanarZ2Subgraph, nullity P.G = 1 → Nat.card (jcb_BoundedRegion P) = 1) ∧
    Nat.card (jcb_BoundedRegion jbc_Pce) = 1 ∧
    Nat.card (jcb_BoundedRegion jcb_LPce) = 1 ∧
    ndt_StarHull jcb_diagK ≠ jcb_diagK :=
  ⟨jcb_boundedRegion_card_eq_nullity, jcb_boundedRegion_card_eq_one_of_nullity_one,
    jcb_square_uniqueBoundedRegion, jcb_Lshape_uniqueBoundedRegion, jcb_diagK_not_own_starHull⟩

end Lattice
end StatMech
