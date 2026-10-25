/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusLocalAngularSplit.Part4
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitEmbedding


namespace StatMech.FrontierA

open SimpleGraph

theorem triangularTorusSplitOffset_injective :
    Function.Injective triangularTorusSplitOffset := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusSplitOffset] at h ⊢

@[simp] theorem triangularTorusSplitOffset_fst_lt_three (a : Fin 6) :
    (triangularTorusSplitOffset a).1 < 3 := by
  fin_cases a <;> decide

@[simp] theorem triangularTorusSplitOffset_snd_lt_three (a : Fin 6) :
    (triangularTorusSplitOffset a).2 < 3 := by
  fin_cases a <;> decide

theorem triangularTorusSplitEmbedCoord_lt
    (L : Nat) [Fact (2 < L)] (z : ZMod L) (c : Nat) (hc : c < 3) :
    3 * z.val + c < 3 * L := by
  have hz := z.val_lt
  omega


end StatMech.FrontierA
