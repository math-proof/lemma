/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossingV.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WalkCrossing.Part4


namespace StatMech.Onsager.WalkCrossingV

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing

variable {n : ℕ} [NeZero n]


theorem fst_step_bound (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n) :
    (pos d (k + 1)).1 = (pos d k).1 ∨ (pos d (k + 1)).1 = (pos d k).1 + 1 ∨
      (pos d (k + 1)).1 = (pos d k).1 - 1 := by
  have h := stepOf_fst (d k)
  rw [fst_step d hclosed k]; omega


end StatMech.Onsager.WalkCrossingV
