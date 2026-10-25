/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part3
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLocalPatternWeight_eq_pow
    (c : Real) (p : SixVertexLocalIncomingPattern) (hp : p.Ice) :
    sixVertexLocalPatternWeight c p =
      c ^ (if p.IsCType then 1 else 0) := by
  unfold sixVertexLocalPatternWeight
  rw [if_pos hp]
  by_cases hpc : p.IsCType <;> simp [hpc]


theorem exists_sixVertexLocalSwapTwo_weight_product_le
    {c : Real} (hc : 1 <= c)
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice) (hd : p d ≠ q d)
    (hnotCC : Not (p.IsCType /\ q.IsCType)) :
    exists e : Fin 4,
      e ≠ d /\ p e ≠ q e /\
      (sixVertexLocalSwapTwo p q d e).1.Ice /\
      (sixVertexLocalSwapTwo p q d e).2.Ice /\
      sixVertexLocalPatternWeight c p * sixVertexLocalPatternWeight c q <=
        sixVertexLocalPatternWeight c
            (sixVertexLocalSwapTwo p q d e).1 *
          sixVertexLocalPatternWeight c
            (sixVertexLocalSwapTwo p q d e).2 := by
  obtain ⟨e, hed, heq, hp', hq', hcount⟩ :=
    exists_sixVertexLocalSwapTwo_of_disagreement p q d hp hq hd hnotCC
  refine ⟨e, hed, heq, hp', hq', ?_⟩
  rw [sixVertexLocalPatternWeight_eq_pow c p hp,
    sixVertexLocalPatternWeight_eq_pow c q hq,
    sixVertexLocalPatternWeight_eq_pow c _ hp',
    sixVertexLocalPatternWeight_eq_pow c _ hq', ← pow_add, ← pow_add]
  exact pow_le_pow_right₀ hc hcount


end
end StatMech.FrontierD
