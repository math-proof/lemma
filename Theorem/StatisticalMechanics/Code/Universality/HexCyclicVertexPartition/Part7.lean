/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Def.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part5


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


@[simp] theorem mem_hexKOneBaseTurns (R : HexFiniteRegion)
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0) (j : Fin 3)
    (ts : List ℤ) :
    ts ∈ hexKOneBaseTurns R a h0 v du hdu j ↔
      ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu ∧
        specialMidCount a h0 v du ts = 1 ∧
        (ofTurns a h0 ts).EndsAt (labelMid v du j) := by
  classical
  simp [hexKOneBaseTurns]


end
end StatMech.Universality
