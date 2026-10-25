/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean -/

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
import Def.StatisticalMechanics.Code.Lattice.EarExistence.Part3
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem extremeCell_orbit_one_le_leftCornerCount (K : Set (Site 2)) (hK : K.Finite)
    (c : Site 2) (hc : IsExtremeCell K c) :
    1 ≤ leftCornerCount K (extremeBase K c hc).1 (dartOrbitPeriod K (extremeBase K c hc)) := by
  apply one_le_leftCornerCount_of_first
  · exact dartOrbitPeriod_pos K hK (extremeBase K c hc)
  · show turnZ K (leftDart c) = -1
    exact extremeCell_turnZ K c hc


theorem extremeCell_orbit_rightCornerCount_lt_period (K : Set (Site 2)) (hK : K.Finite)
    (c : Site 2) (hc : IsExtremeCell K c) :
    rightCornerCount K (extremeBase K c hc).1 (dartOrbitPeriod K (extremeBase K c hc)) <
      (dartOrbitPeriod K (extremeBase K c hc) : ℤ) := by
  have hpart := orbitStep_partition K (extremeBase K c hc).1 (dartOrbitPeriod K (extremeBase K c hc))
  have hleft := extremeCell_orbit_one_le_leftCornerCount K hK c hc
  have hstraight : (0 : ℤ) ≤ straightStepCount K (extremeBase K c hc).1
      (dartOrbitPeriod K (extremeBase K c hc)) := by
    unfold straightStepCount; positivity
  linarith


theorem removeCell_finite (K : Set (Site 2)) (hK : K.Finite) (c : Site 2) :
    (K \ {c}).Finite :=
  hK.subset Set.diff_subset


theorem removeCell_ncard_lt (K : Set (Site 2)) (hK : K.Finite) (c : Site 2) (hc : c ∈ K) :
    (K \ {c}).ncard < K.ncard := by
  have hsub : (K \ {c}) ⊂ K := by
    rw [Set.ssubset_iff_of_subset Set.diff_subset]
    exact ⟨c, hc, by simp⟩
  exact Set.ncard_lt_ncard hsub hK


theorem removeExtremeCell_ncard_lt (K : Set (Site 2)) (hK : K.Finite) (c : Site 2)
    (hc : IsExtremeCell K c) : (K \ {c}).ncard < K.ncard :=
  removeCell_ncard_lt K hK c hc.mem


end Lattice
end StatMech
