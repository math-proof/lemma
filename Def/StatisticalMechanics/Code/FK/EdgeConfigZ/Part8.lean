/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Theorem.StatisticalMechanics.Code.FK.CenteredFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Instance.StatisticalMechanics.Code.FK.EdgeConfigZ.Part2
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


section BoxNesting

variable {d : ℕ}


noncomputable def ecz_subBoxIso (a n : ℕ) (hle : a ≤ n) :
    boxGraph d a ≃g agl_left (boxGraph d n) (ecz_subBoxPred d a n) := by
  classical
  have hsub : box d a ⊆ box d n := box_mono d hle
  refine agl_leftBlockIso n a (ecz_subBoxPred d a n) 0 ?_ ?_
  · exact {
      toFun := fun y => ⟨⟨(y : Site d), hsub y.2⟩, y.2⟩
      invFun := fun z => ⟨(z.1 : Site d), z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · intro y
    show ((⟨(y : Site d), hsub y.2⟩ : boxVerts d n) : Site d) = (y : Site d) + 0
    simp


end BoxNesting
end FK
end StatMech
