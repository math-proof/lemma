/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCurrentGraph.Part3
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaCurrentCoupling_reflect
    (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (e : Sym2 (LPReplicaCurrentVertex V)) :
    lpReplicaCurrentCoupling J hf r
        (Sym2.map lpReplicaCurrentReflect e) =
      lpReplicaCurrentCoupling J hf r e := by
  induction e with
  | h a b =>
      rcases a with (a | g) <;> rcases b with (b | h)
      · rcases a with a | a <;> rcases b with b | b <;> rfl
      · rcases a with a | a <;> cases h <;> rfl
      · cases g <;> rcases b with b | b <;> rfl
      · cases g <;> cases h <;> rfl

omit [Fintype V] [DecidableEq V] in
theorem lpReplicaCurrentCoupling_nonneg
    (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hJ : ∀ e, 0 <= J e) (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (e : Sym2 (LPReplicaCurrentVertex V)) :
    0 <= lpReplicaCurrentCoupling J hf r e := by
  induction e with
  | h a b =>
      rcases a with (a | g) <;> rcases b with (b | h)
      · rcases a with a | a <;> rcases b with b | b
        · exact hJ _
        · exact hr
        · exact hr
        · exact hJ _
      · rcases a with a | a <;> cases h <;>
          simp only [lpReplicaCurrentCoupling, Sym2.lift_mk]
        · exact hhf _
        · exact le_rfl
        · exact le_rfl
        · exact hhf _
      · cases g <;> rcases b with b | b <;>
          simp only [lpReplicaCurrentCoupling, Sym2.lift_mk]
        · exact hhf _
        · exact le_rfl
        · exact le_rfl
        · exact hhf _
      · cases g <;> cases h <;> exact le_rfl

end
end StatMech.Ising
