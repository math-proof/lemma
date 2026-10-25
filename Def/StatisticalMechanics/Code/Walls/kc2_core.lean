/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
import Theorem.StatisticalMechanics.Code.Walls.kc2_supportisface
import Theorem.StatisticalMechanics.Code.Walls.kc2_dartdircases
import Theorem.StatisticalMechanics.Code.Walls.kc2_rightfaceinK
import Theorem.StatisticalMechanics.Code.Walls.kc2_downfaceoutK
import Theorem.StatisticalMechanics.Code.Walls.kc2_leftupfacecell.Part2
import Theorem.StatisticalMechanics.Code.Walls.kc2_core
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


def kc2_SupportOddNonRight (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ z ∈ (mpl_orbitLoop K a).support, ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) →
    ∀ e : Dart, IsBoundaryDart K e → z = dartFace e →
      (e.dir = ![0, -1] ∨ e.dir = ![0, 1] ∨ e.dir = ![-1, 0]) → z ∈ K


end Walls
end StatMech
