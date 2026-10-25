/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIncidentStairPatch.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStaircaseAssembly.Part2


namespace StatMech.FrontierA

open scoped NNReal

open Set


def kwStairEvenLocal {S : ℕ} [NeZero S] (k : Fin S) : Fin (2 * S) :=
  ⟨2 * k.val, by have := k.isLt; omega⟩

def kwStairOddLocal {S : ℕ} [NeZero S] (k : Fin S) : Fin (2 * S) :=
  ⟨2 * k.val + 1, by have := k.isLt; omega⟩

def kwStairSliceIndex {S : ℕ} [NeZero S] (l : Fin (2 * S)) : Fin S :=
  ⟨l.val / 2, by
    have hl := l.isLt
    have hS : 0 < S := NeZero.pos S
    omega⟩

end StatMech.FrontierA
