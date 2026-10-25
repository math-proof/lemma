/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceComponentBijection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.RotationSystemFaces.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

noncomputable def rsf_componentDarts {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    (fcb_offComplGraph Vc).ConnectedComponent → Set Dart :=
  ConnectedComponent.lift
    (fun v => {e : Dart | IsBoundaryDart (offSupportComponent Vc (v : Site 2)) e})
    (by
      intro u v p _
      simp only
      rw [rsf_fcb_reachable_offSupportComponent_eq Vc ⟨p⟩])

end Lattice
end StatMech
