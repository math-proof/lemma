/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.AlgebraicCombinatorics.code.HasseWalkFormula.Part2
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.HasseWalkFormula
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkTypeCount
import Def.v1.Atlas.AlgebraicCombinatorics.code.WalkTypeCount
import Mathlib.Combinatorics.Young.YoungDiagram
set_option autoImplicit false

open scoped Nat
open HasseWalkFormula HasseWalks


section YoungDiagramFinset

lemma finite_youngDiagrams_of_size (n : ℕ) :
    Set.Finite {μ : YoungDiagram | μ.card = n} := by
  have hinj : Set.InjOn YoungDiagram.cells {μ : YoungDiagram | μ.card = n} := by
    intro a _ b _ h
    rwa [YoungDiagram.ext_iff]
  have hmaps : Set.MapsTo YoungDiagram.cells
      {μ : YoungDiagram | μ.card = n}
      ↑((Finset.range n ×ˢ Finset.range n).powerset : Finset (Finset (ℕ × ℕ))) := by
    intro μ (hμ : μ.card = n)
    simp only [Finset.mem_coe, Finset.mem_powerset]
    rw [← hμ]; exact μ.cells_subset_range_sq
  exact Set.Finite.of_injOn hmaps hinj (Finset.finite_toSet _)

end YoungDiagramFinset
