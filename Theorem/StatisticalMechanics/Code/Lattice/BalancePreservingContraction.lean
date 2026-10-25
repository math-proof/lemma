/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BalanceContraction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnetEar
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem bpc_dartNext_agree (K K' : Set (Site 2)) (e : Dart)
    (h1 : (e.head + (-rot90Fun e.dir) ∈ K') ↔ (e.head + (-rot90Fun e.dir) ∈ K))
    (h2 : (e.tail + (-rot90Fun e.dir) ∈ K') ↔ (e.tail + (-rot90Fun e.dir) ∈ K)) :
    dartNext K' e = dartNext K e := by
  classical
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [dartNext_of_front_mem K' e (h1.mpr hA), dartNext_of_front_mem K e hA]
  · by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [dartNext_of_side_mem K' e (fun hh => hA (h1.mp hh)) (h2.mpr hB),
          dartNext_of_side_mem K e hA hB]
    · rw [dartNext_of_corner K' e (fun hh => hA (h1.mp hh)) (fun hh => hB (h2.mp hh)),
          dartNext_of_corner K e hA hB]


theorem bpc_turnZ_agree (K K' : Set (Site 2)) (e : Dart)
    (h1 : (e.head + (-rot90Fun e.dir) ∈ K') ↔ (e.head + (-rot90Fun e.dir) ∈ K))
    (h2 : (e.tail + (-rot90Fun e.dir) ∈ K') ↔ (e.tail + (-rot90Fun e.dir) ∈ K)) :
    turnZ K' e = turnZ K e := by
  classical
  unfold turnZ
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [if_pos (h1.mpr hA), if_pos hA]
  · rw [if_neg (fun hh => hA (h1.mp hh)), if_neg hA]
    by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [if_pos (h2.mpr hB), if_pos hB]
    · rw [if_neg (fun hh => hB (h2.mp hh)), if_neg hB]


end Lattice
end StatMech
