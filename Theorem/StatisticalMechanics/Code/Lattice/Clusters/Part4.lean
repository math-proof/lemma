/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part4
open Set


namespace StatMech

namespace Lattice

variable {d : ℕ}


@[simp]
theorem mem_cluster {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d} :
    y ∈ cluster d ω x ↔ Connected d ω x y := Iff.rfl


theorem self_mem_cluster (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    x ∈ cluster d ω x := connected_refl ω x


theorem cluster_eq_of_connected {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (h : Connected d ω x y) : cluster d ω x = cluster d ω y := by
  ext z
  simp only [mem_cluster]
  exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩


end Lattice
end StatMech
