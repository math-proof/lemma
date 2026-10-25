/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean -/

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
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

def ksc_KingSaturated {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (T : Set (Site 2)) : Prop :=
  ∀ u v : Site 2, u ∈ T → v ∈ jil_offSupportInterior Vc → mci_kingGraph.Adj u v → v ∈ T


def ksc_NoKingSeparation {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) : Prop :=
  ∀ T : Set (Site 2), seed ∈ T → T ⊆ jil_offSupportInterior Vc →
    ksc_KingSaturated Vc T → jil_offSupportInterior Vc ⊆ T


end Lattice
end StatMech
