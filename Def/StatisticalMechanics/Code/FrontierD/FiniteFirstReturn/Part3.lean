/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part2


namespace StatMech.FrontierD

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def finiteFirstReturnPerm
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] : Equiv.Perm {a : A // selected a} :=
  Equiv.ofBijective (finiteFirstReturn sigma selected)
    ((Fintype.bijective_iff_injective_and_card
      (finiteFirstReturn sigma selected)).2
        ⟨finiteFirstReturn_injective sigma selected, rfl⟩)

end
end StatMech.FrontierD
