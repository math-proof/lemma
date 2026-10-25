/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part4


namespace StatMech.FrontierD

noncomputable section

def fkRectFiniteEventUnion {R : FKRectTorus} {ι : Type*}
    (s : Finset ι) (A : ι → Set R.Configuration) : Set R.Configuration :=
  {omega | ∃ i ∈ s, omega ∈ A i}


end
end StatMech.FrontierD
