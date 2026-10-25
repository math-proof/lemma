/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part3
open Set Finset


namespace StatMech

namespace Lattice

@[simp]
theorem mem_box {d n : ℕ} {x : Site d} : x ∈ box d n ↔ ∀ i, (x i).natAbs ≤ n := Iff.rfl


theorem box_finite (d n : ℕ) : (box d n).Finite := by
  apply Set.Finite.subset
    (Set.Finite.pi (fun _ : Fin d => Set.finite_Icc (-(n : ℤ)) (n : ℤ)))
  intro x hx i _
  rw [Set.mem_Icc]
  have hx' : (x i).natAbs ≤ n := hx i
  have habs : |x i| ≤ (n : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hx'
  exact abs_le.mp habs


end Lattice
end StatMech
