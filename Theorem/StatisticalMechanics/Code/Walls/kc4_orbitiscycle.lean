/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_orbitiscycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem kc4_orbitFaceLoop_isCycle (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1))
      (Set.Iio (dartOrbitPeriod K a))) :
    (mpl_orbitFaceLoop K a).IsCycle :=
  mpl_orbitFaceLoop_isCycle K a hp hinj


theorem kc4_OrbitIsCycle (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1))
      (Set.Iio (dartOrbitPeriod K a))) :
    (mpl_orbitLoop K a).IsCycle := by
  
  have hdual : (mpl_orbitFaceLoop K a).IsCycle := kc4_orbitFaceLoop_isCycle K a hp hinj
  
  have hprimal : ((mpl_orbitFaceLoop K a).mapLe (faceBoundaryGraph_le K)).IsCycle :=
    hdual.mapLe (faceBoundaryGraph_le K)
  
  rwa [mpl_orbitLoop]


theorem kc4_orbitIsCycle_support_nodup (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1))
      (Set.Iio (dartOrbitPeriod K a))) :
    (mpl_orbitLoop K a).support.tail.Nodup :=
  (kc4_OrbitIsCycle K a hp hinj).support_nodup


theorem kc4_orbitIsCycle_count_support_of_mem (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1))
      (Set.Iio (dartOrbitPeriod K a)))
    {v : Site 2} (hv : v ∈ (mpl_orbitLoop K a).support) (hvb : v ≠ dartFace a.1) :
    (mpl_orbitLoop K a).support.count v = 1 :=
  (kc4_OrbitIsCycle K a hp hinj).count_support_of_mem hv hvb


theorem kc4_orbitIsCycle_count_support (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1))
      (Set.Iio (dartOrbitPeriod K a))) :
    (mpl_orbitLoop K a).support.count (dartFace a.1) = 2 :=
  (kc4_OrbitIsCycle K a hp hinj).count_support


theorem kc4_unitCell_faceInj :
    Set.InjOn (fun k => dartFace ((dartNext unitCell)^[k] ucBase.1))
      (Set.Iio (dartOrbitPeriod unitCell ucBase)) := by
  rw [unitCell_orbitPeriod_eq_four, show ucBase.1 = ucDart0 from rfl]
  exact unitCell_orbitFace_injOn


theorem kc4_unitCell_orbitIsCycle : (mpl_orbitLoop unitCell ucBase).IsCycle :=
  kc4_OrbitIsCycle unitCell ucBase
    (by rw [unitCell_orbitPeriod_eq_four]; norm_num)
    kc4_unitCell_faceInj

end Walls
end StatMech
