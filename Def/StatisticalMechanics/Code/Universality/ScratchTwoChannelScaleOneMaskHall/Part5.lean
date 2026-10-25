/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part2


namespace StatMech.Universality

noncomputable def rlcScaleOneSectionBListEquiv :
    Equiv (Fin rlcScaleOneSectionBList.length) RlcScaleOneSectionBFailure :=
  ((Finset.nodup_toList _).getEquiv _).trans
    { toFun := fun w => ⟨w.1, (rlcScaleOneSectionBList_mem w.1).mp w.2⟩
      invFun := fun w => ⟨w.1, (rlcScaleOneSectionBList_mem w.1).mpr w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

noncomputable def rlcScaleOneSectionCListEquiv :
    Equiv (Fin rlcScaleOneSectionCList.length) RlcScaleOneSectionCFailure :=
  ((Finset.nodup_toList _).getEquiv _).trans
    { toFun := fun w => ⟨w.1, (rlcScaleOneSectionCList_mem w.1).mp w.2⟩
      invFun := fun w => ⟨w.1, (rlcScaleOneSectionCList_mem w.1).mpr w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end StatMech.Universality
