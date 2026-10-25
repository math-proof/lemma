/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcExteriorClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ArcNoSeparation.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ArcExteriorClose
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

noncomputable def arcxc_extToOffSupportHom {B : Set (Site 2)} {R : ℕ} (hB : B ⊆ box 2 R) :
    (hypercubicLattice 2).induce (exterior 2 R) →g ffc_offSupportLattice B where
  toFun := fun z => (z : Site 2)
  map_rel' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hadj
    exact arcxc_exterior_adj_offSupport hB hx hy hadj


end Lattice
end StatMech
