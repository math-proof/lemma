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
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem wtc_touching_iff_probes (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (i : ℕ) :
    ¬ jc4_FootprintFree K a r i ↔ jc5_ProbesEarFootprint r ((dartNext K)^[i] a.1) := by
  unfold jc4_FootprintFree
  exact jc5_not_avoidsEarFootprint_iff_probes r _


theorem wtc_free_iff_avoids (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (i : ℕ) :
    jc4_FootprintFree K a r i ↔ jc3_AvoidsEarFootprint r ((dartNext K)^[i] a.1) :=
  Iff.rfl


end Walls
end StatMech
