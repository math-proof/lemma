/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_oddrayeqleftRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
import Theorem.StatisticalMechanics.Code.Walls.kc2_core.Part3
import Def.StatisticalMechanics.Code.Walls.kc3_oddrayeqleftRegion
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem kc3_supportOddInK_iff_leftRegion_subset {K : Set (Site 2)}
    {a : {e : Dart // IsBoundaryDart K e}} :
    exc_SupportOddInK K a ↔ kc3_LeftRegionSupportSubset K a := by
  unfold exc_SupportOddInK kc3_LeftRegionSupportSubset
  constructor
  · intro h z hz
    obtain ⟨hzL, hzs⟩ := hz
    rw [jec_mem_leftRegion] at hzL
    exact h z hzs hzL
  · intro h z hzs hodd
    exact h ⟨(jec_mem_leftRegion _ z).mpr hodd, hzs⟩


theorem kc3_supportOddInK_of_leftRegion_subset {K : Set (Site 2)}
    {a : {e : Dart // IsBoundaryDart K e}} (h : kc3_LeftRegionSupportSubset K a) :
    exc_SupportOddInK K a :=
  kc3_supportOddInK_iff_leftRegion_subset.mpr h


theorem kc3_leftRegion_subset_of_three {K : Set (Site 2)}
    {a : {e : Dart // IsBoundaryDart K e}}
    (hdown : kc2_DownFaceEven K a) (hup : kc2_UpFaceInK K a) (hleft : kc2_LeftFaceInK K a) :
    kc3_LeftRegionSupportSubset K a :=
  kc3_supportOddInK_iff_leftRegion_subset.mp (kc2_supportOddInK_of_three hdown hup hleft)


theorem kc3_leftRegion_subset_iff_three {K : Set (Site 2)}
    {a : {e : Dart // IsBoundaryDart K e}} :
    kc3_LeftRegionSupportSubset K a ↔
      (kc2_DownFaceEven K a ∧ kc2_UpFaceInK K a ∧ kc2_LeftFaceInK K a) :=
  kc3_supportOddInK_iff_leftRegion_subset.symm.trans kc2_core_iff_three


theorem kc3_unitCell_leftRegion_subset :
    kc3_LeftRegionSupportSubset unitCell ucBase :=
  kc3_supportOddInK_iff_leftRegion_subset.mp kc2_unitCell_core

end Walls
end StatMech
