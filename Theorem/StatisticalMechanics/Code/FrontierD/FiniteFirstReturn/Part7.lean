/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part7


namespace StatMech.FrontierD

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem finiteFirstReturnOccurrencePoint_succ
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (x : FiniteFirstReturnOccurrenceIndex sigma selected states)
    (hnext : x.2.val + 1 <
      finiteFirstReturnTime sigma selected (states.get x.1)) :
    sigma (finiteFirstReturnOccurrencePoint sigma selected states x) =
      finiteFirstReturnOccurrencePoint sigma selected states
        (finiteFirstReturnOccurrenceIndexSucc
          sigma selected states x hnext) := by
  simp [finiteFirstReturnOccurrencePoint,
    finiteFirstReturnOccurrenceIndexSucc, pow_succ', Equiv.Perm.mul_apply]

theorem finiteFirstReturnOccurrencePoint_last
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (x : FiniteFirstReturnOccurrenceIndex sigma selected states)
    (hlast : x.2.val + 1 =
      finiteFirstReturnTime sigma selected (states.get x.1)) :
    sigma (finiteFirstReturnOccurrencePoint sigma selected states x) =
      (finiteFirstReturn sigma selected (states.get x.1)).1 := by
  change sigma ((sigma ^ x.2.val) (states.get x.1).1) =
    (sigma ^ finiteFirstReturnTime sigma selected (states.get x.1))
      (states.get x.1).1
  calc
    sigma ((sigma ^ x.2.val) (states.get x.1).1) =
        (sigma ^ (x.2.val + 1)) (states.get x.1).1 := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    _ = (sigma ^ finiteFirstReturnTime sigma selected (states.get x.1))
        (states.get x.1).1 := by rw [hlast]

theorem finiteFirstReturnOccurrencePoint_step_interior
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected]
    (states : List {a : A // selected a})
    (i : Fin states.length) (k : Nat)
    (hk : k + 1 < finiteFirstReturnTime sigma selected (states.get i)) :
    sigma (finiteFirstReturnOccurrencePoint sigma selected states
        ⟨i, ⟨k, by omega⟩⟩) =
      finiteFirstReturnOccurrencePoint sigma selected states
        ⟨i, ⟨k + 1, hk⟩⟩ := by
  simp only [finiteFirstReturnOccurrencePoint]
  rw [show k + 1 = Nat.succ k by omega, pow_succ']
  rfl

theorem finiteFirstReturnOccurrencePoint_step_endpoint
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected]
    (states : List {a : A // selected a})
    (i : Fin states.length) (k : Nat)
    (hk : k < finiteFirstReturnTime sigma selected (states.get i))
    (hlast : k + 1 =
      finiteFirstReturnTime sigma selected (states.get i)) :
    sigma (finiteFirstReturnOccurrencePoint sigma selected states
        ⟨i, ⟨k, hk⟩⟩) =
      (finiteFirstReturn sigma selected (states.get i)).1 := by
  simp only [finiteFirstReturnOccurrencePoint, finiteFirstReturn]
  rw [← hlast, show k + 1 = Nat.succ k by omega, pow_succ']
  rfl

end
end StatMech.FrontierD
