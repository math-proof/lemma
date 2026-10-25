/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalkFormula.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.NormalOrderCoeff.Part2
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.NormalOrderCoeff
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.HasseWalks
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkCountOps
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkCountBridge
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkOperatorLemmas
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.HasseWalks
import Def.v1.Atlas.AlgebraicCombinatorics.code.WalkCountOps
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WalkCountBridge.Part2
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WalkOperatorLemmas
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Combinatorics.Young.YoungDiagram
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.HasseWalkFormula.Part2
set_option autoImplicit false

open scoped Nat


instance HasseWalkFormula.upWalkType_finite (m : ℕ) (mu : YoungDiagram) :
    Finite (HasseWalkFormula.UpWalkType m mu) :=
  Finite.of_injective
    (fun ⟨w, h0, he, hs⟩ (i : Fin (m + 1)) =>
      (⟨(w ⟨i.val, i.isLt⟩).cells,
        Finset.mem_powerset.mpr
          (HasseWalkFormula.upWalkType_cells_subset w h0 hs he ⟨i.val, i.isLt⟩)⟩ :
        ↑(mu.cells.powerset)))
    (fun ⟨w1, h01, he1, hs1⟩ ⟨w2, h02, he2, hs2⟩ heq => by
      apply Subtype.ext; funext ⟨i, hi⟩
      have := congr_fun heq ⟨i, hi⟩
      simp at this
      exact YoungDiagram.ext_iff.mpr this)

