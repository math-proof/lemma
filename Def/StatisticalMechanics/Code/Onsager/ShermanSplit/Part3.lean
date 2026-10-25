/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanSplit.Part2


namespace StatMech.Onsager

open Matrix BigOperators Finset Complex

set_option linter.unusedSectionVars false

section Split

variable {E : Type*} [DecidableEq E]


def ons_firstReturnSplit (e : E) : List E → List (List E)
  | [] => []
  | x :: r =>
      match hpost : r.dropWhile (fun y => y ≠ e) with
      | [] => [x :: r]
      | e' :: post' =>
          (x :: r.takeWhile (fun y => y ≠ e) ++ [e']) :: ons_firstReturnSplit e (e' :: post')
  termination_by l => l.length
  decreasing_by
    have hle := List.length_dropWhile_le (fun y => decide (y ≠ e)) r
    rw [hpost] at hle
    simp only [List.length_cons] at hle ⊢
    omega


end Split
end StatMech.Onsager
