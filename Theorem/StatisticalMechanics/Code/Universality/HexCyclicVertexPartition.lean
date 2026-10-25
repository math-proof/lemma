/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Def.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


@[simp] theorem hexCyclicSucc_pred (j : Fin 3) :
    hexCyclicSucc (hexCyclicPred j) = j := by
  fin_cases j <;> rfl

@[simp] theorem hexCyclicPred_succ (j : Fin 3) :
    hexCyclicPred (hexCyclicSucc j) = j := by
  fin_cases j <;> rfl


theorem hexCyclicSucc_mid (v du : ℂ) (j : Fin 3) :
    labelMid v du (hexCyclicSucc j) =
      v + hexOmega * (labelMid v du j - v) := by
  have hcube : hexOmega ^ 3 = 1 := hexOmega_primRoot.pow_eq_one
  fin_cases j
  · simp [hexCyclicSucc, labelMid]
  · simp [hexCyclicSucc, labelMid]
    ring
  · simp [hexCyclicSucc, labelMid]
    rw [show hexOmega * (hexOmega ^ 2 * du) = hexOmega ^ 3 * du by ring,
      hcube, one_mul]


theorem hexCyclicPred_mid (v du : ℂ) (j : Fin 3) :
    labelMid v du (hexCyclicPred j) =
      v + hexOmega ^ 2 * (labelMid v du j - v) := by
  have hcube : hexOmega ^ 3 = 1 := hexOmega_primRoot.pow_eq_one
  fin_cases j <;> simp [hexCyclicPred, labelMid]
  · rw [show hexOmega ^ 2 * (hexOmega * du) = hexOmega ^ 3 * du by ring,
      hcube, one_mul]
  · rw [show hexOmega ^ 2 * (hexOmega ^ 2 * du) = hexOmega * (hexOmega ^ 3 * du) by ring,
      hcube, one_mul]


end
end StatMech.Universality
