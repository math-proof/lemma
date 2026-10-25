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
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem wch_bridge_false (Vc : (hypercubicLattice 2).Walk a a) :
    ¬ wpj_PlaneDualityBridge Vc := by
  rintro ⟨hoffIn, hoffOut, -, -, -, -⟩
  have ha : a ∈ Vc.support := Vc.start_mem_support
  by_cases h : a ∈ jec_leftRegion Vc
  · exact hoffIn a h ha
  · exact hoffOut a h ha


theorem wch_covers_off_pair_false (Vc : (hypercubicLattice 2).Walk a a)
    {sIn sOut : Site 2} (hsInoff : sIn ∉ Vc.support) (hsOutoff : sOut ∉ Vc.support)
    (hcovIn : jec_leftRegion Vc ⊆ offSupportComponent Vc sIn)
    (hcovOut : (jec_leftRegion Vc)ᶜ ⊆ offSupportComponent Vc sOut) : False := by
  have ha : a ∈ Vc.support := Vc.start_mem_support
  by_cases h : a ∈ jec_leftRegion Vc
  · exact offSupportComponent_offSupport Vc hsInoff (hcovIn h) ha
  · exact offSupportComponent_offSupport Vc hsOutoff (hcovOut h) ha


end Lattice
end StatMech
