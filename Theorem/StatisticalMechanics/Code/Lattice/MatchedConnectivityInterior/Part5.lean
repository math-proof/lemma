/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean -/

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
import Def.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior.Part5
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem mci_kingRowLinked_of_kingStepReachable {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc)
    (hstep : ∀ z : jil_offSupportInterior Vc,
      (mci_interiorKingGraph Vc).Reachable z ⟨seed, hseedI⟩) :
    mci_KingRowLinked Vc seed := by
  intro z hz
  obtain ⟨w⟩ := hstep ⟨z, hz⟩
  exact mci_kingStepGraph_walk_interior Vc w


theorem mci_kingRowLinked_of_rowLinked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hlink : jil_RowLinked Vc seed) :
    mci_KingRowLinked Vc seed := by
  intro z hz
  obtain ⟨p, hp⟩ := hlink z hz
  refine ⟨p.mapLe mci_hyper_le_king, ?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_mapLe_eq_support mci_hyper_le_king p] at hw
  exact mci_offSupport_walk_interior Vc p hp hz w hw


end Lattice
end StatMech
