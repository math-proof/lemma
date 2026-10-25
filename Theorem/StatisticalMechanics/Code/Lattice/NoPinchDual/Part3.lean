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
import Def.StatisticalMechanics.Code.Lattice.NoPinchDual.Part3
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem npd_orbitFaceNoPinch_of_noDiagTouch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : npd_NoDiagTouchAlongOrbit K a) :
    OrbitFaceNoPinch K a := by
  intro i hi j hj hface
  have hbi : IsBoundaryDart K ((dartNext K)^[i] a.1) := iterate_isBoundaryDart K a.1 a.2 i
  have hbj : IsBoundaryDart K ((dartNext K)^[j] a.1) := iterate_isBoundaryDart K a.1 a.2 j
  exact npd_noPinch_local_of_noDiagTouch hbi hbj hface (h i hi)


theorem npd_orbitFace_injOn_of_noDiagTouch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : npd_NoDiagTouchAlongOrbit K a) :
    Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) :=
  orbitFace_injOn_of_noPinch K a (npd_orbitFaceNoPinch_of_noDiagTouch K a h)


end Lattice
end StatMech
