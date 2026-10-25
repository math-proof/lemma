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
import Theorem.StatisticalMechanics.Code.Lattice.ArcExteriorClose.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

def arcxc_ReachesExterior (B : Set (Site 2)) (R : ℕ) : Prop :=
  B ⊆ box 2 R ∧
    ∀ x : Site 2, x ∉ B → ∃ (e : Site 2) (p : (hypercubicLattice 2).Walk x e),
      (∀ w ∈ p.support, w ∉ B) ∧ e ∈ exterior 2 R


end Lattice
end StatMech
