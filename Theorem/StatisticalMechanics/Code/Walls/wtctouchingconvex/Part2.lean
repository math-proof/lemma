/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wtctouchingconvex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Walls.jc4_firstreturnK.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc5_core.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc5_footprintdartsfinite
import Def.StatisticalMechanics.Code.Walls.wtctouchingconvex
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem wtc_touchingSteps_injOn (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) :
    Set.InjOn (fun i => (dartNext K)^[i] a.1) (wtc_touchingSteps K a r) := by
  intro i hi j hj h
  have hi' : i < dartOrbitPeriod K a := hi.1
  have hj' : j < dartOrbitPeriod K a := hj.1
  
  have hsub : (dartNextSub K)^[i] a = (dartNextSub K)^[j] a := by
    apply Subtype.ext
    rw [dartNextSub_iterate_val, dartNextSub_iterate_val]
    exact h
  exact jc5_orbit_injOn_Iio K a (Set.mem_Iio.mpr hi') (Set.mem_Iio.mpr hj') hsub


theorem wtc_touchingSteps_finite (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) :
    (wtc_touchingSteps K a r).Finite := by
  apply Set.Finite.of_finite_image (f := fun i => (dartNext K)^[i] a.1) _
    (wtc_touchingSteps_injOn K a r)
  
  apply (jc5_footprintDarts_finite r).subset
  rintro _ ⟨i, hi, rfl⟩
  exact (wtc_touching_iff_probes K a r i).mp hi.2


end Walls
end StatMech
