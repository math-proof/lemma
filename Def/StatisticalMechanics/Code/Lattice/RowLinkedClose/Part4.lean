/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part4
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

def rlc_SegmentDown {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) : Prop :=
  ∀ z ∈ jil_offSupportInterior Vc, z ≠ seed →
    (![z 0 - 1, z 1] : Site 2) ∈ Vc.support →
    ∃ cx : ℤ, z 0 ≤ cx ∧
      (∀ t : ℤ, z 0 ≤ t → t ≤ cx → (![t, z 1] : Site 2) ∉ Vc.support) ∧
      (![cx, z 1 - 1] : Site 2) ∉ Vc.support


end Lattice
end StatMech
