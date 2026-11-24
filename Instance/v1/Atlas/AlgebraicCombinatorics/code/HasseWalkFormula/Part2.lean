module
public import Def.v1.Atlas.AlgebraicCombinatorics.code.NormalOrderCoeff.Part2
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.NormalOrderCoeff
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.HasseWalks
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkCountOps
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkCountBridge
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkOperatorLemmas
public import Theorem.v1.Atlas.AlgebraicCombinatorics.code.HasseWalks
public import Def.v1.Atlas.AlgebraicCombinatorics.code.WalkCountOps
public import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WalkCountBridge.Part2
public import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WalkOperatorLemmas
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Theorem.v1.Atlas.AlgebraicCombinatorics.code.HasseWalkFormula.Part2
set_option autoImplicit false
open scoped Nat


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalkFormula.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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

