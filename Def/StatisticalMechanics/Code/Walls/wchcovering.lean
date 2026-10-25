/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wchcovering.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceComponentBijection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.OutsideConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
import Theorem.StatisticalMechanics.Code.Walls.wpjplanarjordan.Part2
import Theorem.StatisticalMechanics.Code.Walls.wocoutsidetop.Part4
import Theorem.StatisticalMechanics.Code.Walls.wchcovering
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


def wch_InteriorCovering (Vc : (hypercubicLattice 2).Walk a a) (sIn : Site 2) : Prop :=
  ∀ z : Site 2, z ∈ jec_leftRegion Vc → z ∉ Vc.support → z ∈ offSupportComponent Vc sIn


def wch_ExteriorCovering (Vc : (hypercubicLattice 2).Walk a a) (sOut : Site 2) : Prop :=
  ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∉ Vc.support → z ∈ offSupportComponent Vc sOut


def wch_CorrectedBridge (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  (∃ sIn, sIn ∈ jec_leftRegion Vc ∧ sIn ∉ Vc.support ∧ wch_InteriorCovering Vc sIn) ∧
    (∃ sOut, sOut ∉ jec_leftRegion Vc ∧ sOut ∉ Vc.support ∧ wch_ExteriorCovering Vc sOut)


end Lattice
end StatMech
