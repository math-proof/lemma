/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn


namespace StatMech.FrontierD

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem finiteFirstReturnTime_pos
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) :
    0 < finiteFirstReturnTime sigma selected x :=
  (Nat.find_spec (finiteReturnWitness sigma selected x)).1

theorem finiteFirstReturnTime_selected
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) :
    selected ((sigma ^ finiteFirstReturnTime sigma selected x) x.1) :=
  (Nat.find_spec (finiteReturnWitness sigma selected x)).2

theorem finiteFirstReturnTime_minimal
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a})
    (n : Nat) (hn : n < finiteFirstReturnTime sigma selected x) :
    Not (0 < n /\ selected ((sigma ^ n) x.1)) :=
  Nat.find_min (finiteReturnWitness sigma selected x) hn

end
end StatMech.FrontierD
