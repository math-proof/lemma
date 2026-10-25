/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.kc9core
import Theorem.StatisticalMechanics.Code.Walls.kc16wallfollow.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


def kc16_ClearEscapeColumn (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) : Prop :=
  ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∉ Vc.support → z 0 ≤ (R : ℤ) →
    (![z 0 + 1, z 1] : Site 2) ∈ Vc.support →
    (z 1 ≤ (R : ℤ) ∧ ∀ j : ℕ, j ≤ ((R : ℤ) + 1 - z 1).toNat →
        (![z 0, z 1 + (j : ℤ)] : Site 2) ∉ Vc.support) ∨
    (-(R : ℤ) ≤ z 1 ∧ ∀ j : ℕ, j ≤ ((R : ℤ) + 1 + z 1).toNat →
        (![z 0, z 1 - (j : ℤ)] : Site 2) ∉ Vc.support)


end Walls
end StatMech
