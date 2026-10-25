/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn


namespace StatMech.FrontierD

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def finiteFirstReturn
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) :
    {a : A // selected a} :=
  ⟨(sigma ^ finiteFirstReturnTime sigma selected x) x.1,
    finiteFirstReturnTime_selected sigma selected x⟩

end
end StatMech.FrontierD
