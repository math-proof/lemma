/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Def.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem npd_noDiagTouchAlongOrbit_of_global {K : Set (Site 2)} (h : npd_NoDiagTouch K)
    (a : {e : Dart // IsBoundaryDart K e}) : npd_NoDiagTouchAlongOrbit K a :=
  fun k _ => h (dartFace ((dartNext K)^[k] a.1))


theorem npd_orbitFaceNoPinch_of_globalNoDiagTouch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : npd_NoDiagTouch K) :
    OrbitFaceNoPinch K a :=
  npd_orbitFaceNoPinch_of_noDiagTouch K a (npd_noDiagTouchAlongOrbit_of_global h a)


theorem npd_diagTouch_example :
    npd_DiagTouch ({![0, 0], ![1, 1]} : Set (Site 2)) ![0, 0] := by
  left
  refine ⟨?_, ?_, ?_, ?_⟩
  · show npd_P00 (![0, 0] : Site 2) ∈ ({![0, 0], ![1, 1]} : Set (Site 2))
    left; funext i; fin_cases i <;> rfl
  · show npd_P11 (![0, 0] : Site 2) ∈ ({![0, 0], ![1, 1]} : Set (Site 2))
    right; funext i; fin_cases i <;> simp [npd_P11]
  · show npd_P10 (![0, 0] : Site 2) ∉ ({![0, 0], ![1, 1]} : Set (Site 2))
    rintro (h | h)
    · have := congrFun h 0; simp [npd_P10] at this
    · have := congrFun h 1; simp [npd_P10] at this
  · show npd_P01 (![0, 0] : Site 2) ∉ ({![0, 0], ![1, 1]} : Set (Site 2))
    rintro (h | h)
    · have := congrFun h 1; simp [npd_P01] at this
    · have := congrFun h 0; simp [npd_P01] at this


end Lattice
end StatMech
