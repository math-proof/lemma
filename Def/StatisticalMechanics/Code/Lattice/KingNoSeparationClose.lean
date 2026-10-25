/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.KingSegmentDownClose
import Theorem.StatisticalMechanics.Code.Lattice.KingDescentAgnosticClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.KingStepConnectClose
import Theorem.StatisticalMechanics.Code.Lattice.KingNoSeparationClose
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

def kns_KingSeparation {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) : Prop :=
  ∃ T : Set (Site 2), seed ∈ T ∧ T ⊆ jil_offSupportInterior Vc ∧
    ksc_KingSaturated Vc T ∧ ∃ z ∈ jil_offSupportInterior Vc, z ∉ T


def kns_ThickPoint {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∃ u v : Site 2, u ∈ Vc.support ∧ v ∈ Vc.support ∧
    (hypercubicLattice 2).Adj u v ∧ s(u, v) ∉ Vc.edges


end Lattice
end StatMech
