/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.FiniteComplementConnected
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.ArcNoSeparation
open Set SimpleGraph


namespace StatMech

namespace Lattice

def arcns_ReachesFarLeft (B : Set (Site 2)) : Prop :=
  ∃ b : ℤ, (∀ q ∈ B, b ≤ q 0) ∧
    ∀ x : Site 2, x ∉ B → ∃ (z0 : Site 2) (p : (hypercubicLattice 2).Walk x z0),
      (∀ w ∈ p.support, w ∉ B) ∧ z0 0 ≤ b - 1


end Lattice
end StatMech
