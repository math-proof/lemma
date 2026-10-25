/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part5


namespace StatMech.FrontierD

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev FiniteFirstReturnOccurrenceIndex
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a}) :=
  (i : Fin states.length) ×
    Fin (finiteFirstReturnTime sigma selected (states.get i))

end
end StatMech.FrontierD
