/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpjplanarjordan.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceComponentBijection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Walls.wpjplanarjordan
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

def wpj_PlaneDualityBridge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  (∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support) ∧
    (∀ s ∉ jec_leftRegion Vc, s ∉ Vc.support) ∧
    (∃ x, x ∈ jec_leftRegion Vc) ∧ (∃ y, y ∉ jec_leftRegion Vc) ∧
    (∃ sIn, jec_leftRegion Vc ⊆ offSupportComponent Vc sIn) ∧
    (∃ sOut, (jec_leftRegion Vc)ᶜ ⊆ offSupportComponent Vc sOut)


end Lattice
end StatMech
