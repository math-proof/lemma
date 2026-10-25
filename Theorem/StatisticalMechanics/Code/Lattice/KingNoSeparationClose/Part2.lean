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
import Def.StatisticalMechanics.Code.Lattice.KingNoSeparationClose
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem kns_kingSeparation_iff_not_noKingSeparation {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2}
    (_hseedI : seed ∈ jil_offSupportInterior Vc) :
    kns_KingSeparation Vc seed ↔ ¬ ksc_NoKingSeparation Vc seed := by
  constructor
  · rintro ⟨T, hseedT, hTsub, hsat, z, hzI, hznT⟩ hns
    exact hznT (hns T hseedT hTsub hsat hzI)
  · intro hns
    rw [ksc_NoKingSeparation] at hns
    push Not at hns
    obtain ⟨T, hseedT, hTsub, hsat, hnsub⟩ := hns
    rw [Set.not_subset] at hnsub
    obtain ⟨z, hzI, hznT⟩ := hnsub
    exact ⟨T, hseedT, hTsub, hsat, z, hzI, hznT⟩


theorem kns_thickPoint_iff_not_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    kns_ThickPoint Vc ↔ ¬ mci_FourThin Vc := by
  constructor
  · rintro ⟨u, v, hu, hv, hadj, hne⟩ hthin
    exact hne (hthin u v hu hv hadj)
  · intro hthin
    rw [mci_FourThin] at hthin
    push Not at hthin
    obtain ⟨u, v, hu, hv, hadj, hne⟩ := hthin
    exact ⟨u, v, hu, hv, hadj, hne⟩


end Lattice
end StatMech
