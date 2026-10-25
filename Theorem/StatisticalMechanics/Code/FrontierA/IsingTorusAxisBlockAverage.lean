/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusAxisMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredBlockAverage
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

variable {Gamma : Type*} [AddCommGroup Gamma]


theorem le_finiteTorusBlockDifferenceAverage
    (G : Gamma → Real) (B : Finset Gamma) (m : Real)
    (hB : B.Nonempty) (hm : ∀ a ∈ B, ∀ b ∈ B, m ≤ G (b - a)) :
    m ≤ finiteTorusBlockDifferenceAverage G B := by
  have hcard : (0 : Real) < B.card := by
    exact_mod_cast hB.card_pos
  have hsum : (B.card : Real) ^ 2 * m ≤
      ∑ a ∈ B, ∑ b ∈ B, G (b - a) := by
    calc
      (B.card : Real) ^ 2 * m =
          ∑ a ∈ B, ∑ _b ∈ B, m := by
        simp
        ring
      _ ≤ ∑ a ∈ B, ∑ b ∈ B, G (b - a) := by
        gcongr with a ha b hb
        exact hm a ha b hb
  unfold finiteTorusBlockDifferenceAverage
  have hcardSq : (0 : Real) < (B.card : Real) ^ 2 := sq_pos_of_pos hcard
  calc
    m = (1 / (B.card : Real) ^ 2) * ((B.card : Real) ^ 2 * m) := by
      field_simp
    _ ≤ (1 / (B.card : Real) ^ 2) *
        ∑ a ∈ B, ∑ b ∈ B, G (b - a) := by
      gcongr

end StatMech.FrontierA
