/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InteriorWindingClose
import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior.Part6
import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.KingInteriorFloodClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.KingSegmentDownClose
import Theorem.StatisticalMechanics.Code.Lattice.KingDescentAgnosticClose
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

def kda_KingDescentStep {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) : Prop :=
  ∀ z ∈ jil_offSupportInterior Vc, z ≠ seed →
    (![z 0 - 1, z 1] : Site 2) ∈ jil_offSupportInterior Vc ∨
    (![z 0 - 1, z 1 - 1] : Site 2) ∈ jil_offSupportInterior Vc ∨
    (![z 0, z 1 - 1] : Site 2) ∈ jil_offSupportInterior Vc ∨
    (![z 0 + 1, z 1 - 1] : Site 2) ∈ jil_offSupportInterior Vc


end Lattice
end StatMech
