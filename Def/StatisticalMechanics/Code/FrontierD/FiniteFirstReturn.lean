/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace StatMech.FrontierD

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def finiteReturnWitness (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) :
    exists n : Nat, 0 < n /\ selected ((sigma ^ n) x.1) := by
  refine ⟨orderOf sigma, orderOf_pos sigma, ?_⟩
  rw [pow_orderOf_eq_one]
  exact x.2

noncomputable def finiteFirstReturnTime
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) : Nat :=
  Nat.find (finiteReturnWitness sigma selected x)

end
end StatMech.FrontierD
