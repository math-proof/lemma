/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part3


namespace StatMech.FrontierD

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def finiteFirstReturnSegment
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) : List A :=
  List.ofFn fun k : Fin (finiteFirstReturnTime sigma selected x) =>
    (sigma ^ k.val) x.1

end
end StatMech.FrontierD
