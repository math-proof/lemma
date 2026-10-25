/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_regionclosed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc2_forcededgeopen.Part2
import Theorem.StatisticalMechanics.Code.Walls.bkm_dccstepopen
import Theorem.StatisticalMechanics.Code.Walls.bc3_regionclosed
open Set
open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc3_ClosedUnderOmega (ω : ConfigSpace (Sym2 (Site d))) (R : Set (Site d)) : Prop :=
  ∀ ⦃x y : Site d⦄, x ∈ R → IsOpenEdge d ω x y → y ∈ R


def bc3_ClosedUnderWiring (G : Finset (Sym2 (Site d))) (R : Set (Site d)) : Prop :=
  ∀ ⦃x y : Site d⦄, x ∈ R → (hypercubicLattice d).Adj x y →
    s(x, y) ∈ G → (0 : Site d) ∉ s(x, y) → y ∈ R


def bc3_ClosedUnderRho (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) (R : Set (Site d)) : Prop :=
  ∀ ⦃x y : Site d⦄, x ∈ R →
    IsOpenEdge d (removeSite 0 (forceOpenFinset G ω)) x y → y ∈ R


end Walls
end StatMech
