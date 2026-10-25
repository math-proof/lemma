/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part6


namespace StatMech.FrontierD

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def finiteFirstReturnOccurrenceIndexSucc
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (x : FiniteFirstReturnOccurrenceIndex sigma selected states)
    (hnext : x.2.val + 1 <
      finiteFirstReturnTime sigma selected (states.get x.1)) :
    FiniteFirstReturnOccurrenceIndex sigma selected states :=
  ⟨x.1, ⟨x.2.val + 1, hnext⟩⟩

end
end StatMech.FrontierD
