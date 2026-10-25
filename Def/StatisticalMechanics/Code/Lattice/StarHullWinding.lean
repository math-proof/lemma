/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness.Part3
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
import Theorem.StatisticalMechanics.Code.Lattice.WindingEarInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.StarHullWinding
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

def shw_MinVertStepLeft (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∃ k < dartOrbitPeriod K a,
    ((dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0) ∧
    (∀ j < dartOrbitPeriod K a,
      (dartFace ((dartNext K)^[j] a.1)) 0 = (dartFace ((dartNext K)^[j + 1] a.1)) 0 →
        (dartFace ((dartNext K)^[k] a.1)) 0 ≤ (dartFace ((dartNext K)^[j] a.1)) 0) ∧
    ((dartNext K)^[k] a.1).dir = ![-1, 0]


end Lattice
end StatMech
