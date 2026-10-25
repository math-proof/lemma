/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Walls.welenterleave.Part2
import Def.StatisticalMechanics.Code.Walls.wdjdufourdjct.Part5
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


attribute [instance] wdj_Hypermap.finD wdj_Hypermap.decD

@[simp] theorem wdj_revPerm_apply (d : Dart) : wdj_revPerm d = d.rev := rfl


theorem wdj_revPerm_involutive : wdj_revPerm * wdj_revPerm = 1 := by
  refine Equiv.ext (fun d => ?_)
  simp only [Equiv.Perm.mul_apply, wdj_revPerm_apply, Dart.rev_rev, Equiv.Perm.one_apply]


theorem wdj_dartNext_injective (K : Set (Site 2)) :
    Function.Injective (dartNextSub K) :=
  dartNextSub_injective K


theorem wdj_winding_is_combinatorial_map (K : Set (Site 2)) :
    (wdj_revPerm * wdj_revPerm = 1) ∧ Function.Injective (dartNextSub K) :=
  ⟨wdj_revPerm_involutive, wdj_dartNext_injective K⟩


theorem wdj_ec_shape (K : wdj_HypermapCounts) :
    K.wdj_ec = K.nv + K.ne + K.nf - K.nd := rfl


theorem wdj_orientationConsistent_beyond_increment :
    ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
      ¬ wel_OrientationConsistent (![1, 1] : Site 2) Vc :=
  ⟨_, wnu_doubleSquare, wel_doubleSquare_not_orientationConsistent⟩


theorem wdj_windingWall_residue_is_orientation
    (hOriented : ∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
      wel_OrientationConsistent (![1, 1] : Site 2) Vc →
        wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) Vc)
    {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : wel_OrientationConsistent (![1, 1] : Site 2) Vc) :
    wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) Vc :=
  hOriented a Vc h

end Lattice
end StatMech
