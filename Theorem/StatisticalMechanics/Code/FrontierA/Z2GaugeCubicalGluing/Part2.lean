/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeSubsystem.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalWilson.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeRectangularThermodynamic
import Theorem.StatisticalMechanics.Code.FrontierA.RectangularBlockTiling
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing
open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.flexible false


namespace StatMech.FrontierA

noncomputable section

variable {E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

variable {Esmall Ebig Psmall Pbig : Type*}
  [Fintype Esmall] [DecidableEq Esmall] [Fintype Ebig] [DecidableEq Ebig]
  [Fintype Psmall] [DecidableEq Psmall] [Fintype Pbig] [DecidableEq Pbig]

@[simp] theorem finOffsetEmbedding_val {n N : Nat} (offset : Nat)
    (h : offset + n ≤ N) (i : Fin n) :
    (finOffsetEmbedding offset h i).val = offset + i.val := rfl

@[simp] theorem finOffsetEmbedding_castSucc {n N : Nat} (offset : Nat)
    (h : offset + n ≤ N) (i : Fin n) :
    finOffsetEmbedding offset (by omega : offset + (n + 1) ≤ N + 1) i.castSucc =
      (finOffsetEmbedding offset h i).castSucc := by
  apply Fin.ext
  rfl

@[simp] theorem finOffsetEmbedding_succ {n N : Nat} (offset : Nat)
    (h : offset + n ≤ N) (i : Fin n) :
    finOffsetEmbedding offset (by omega : offset + (n + 1) ≤ N + 1) i.succ =
      (finOffsetEmbedding offset h i).succ := by
  apply Fin.ext
  rfl

@[simp] theorem finOffsetEmbedding_castSucc' {n N : Nat} (offset : Nat)
    (h : offset + (n + 1) ≤ N + 1) (i : Fin n) :
    finOffsetEmbedding offset h i.castSucc =
      (finOffsetEmbedding offset (by omega) i).castSucc := by
  apply Fin.ext
  rfl

@[simp] theorem finOffsetEmbedding_succ' {n N : Nat} (offset : Nat)
    (h : offset + (n + 1) ≤ N + 1) (i : Fin n) :
    finOffsetEmbedding offset h i.succ =
      (finOffsetEmbedding offset (by omega) i).succ := by
  apply Fin.ext
  rfl

end
end StatMech.FrontierA
