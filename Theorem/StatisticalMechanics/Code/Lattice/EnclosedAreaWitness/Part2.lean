/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.WindingEarInduction.Part3
import Def.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem eaw_windingWitness_of_cycle_interior (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (hnp : OrbitFaceNoPinch K a)
    (hint : eaw_InteriorSubset K a) :
    wei_WindingWitness K a := by
  have hcyc : (mpl_orbitLoop K a).IsCycle :=
    mpl_orbitLoop_isCycle K a hp (orbitFace_injOn_of_noPinch K a hnp)
  obtain ⟨z, hz⟩ := eaw_cycle_oddCell' (mpl_orbitLoop K a) hcyc
  exact ⟨z, hint z hz, hz⟩


end Lattice
end StatMech
