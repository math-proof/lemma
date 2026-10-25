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
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.SumSquaresFactorial
set_option autoImplicit false

open scoped Nat
open HasseWalkFormula HasseWalks


section YoungDiagramFinset

noncomputable def youngDiagramsOfSize (n : ℕ) : Finset YoungDiagram :=
  (finite_youngDiagrams_of_size n).toFinset

def dnUn (n : ℕ) : List HStep :=
  List.replicate n HStep.U ++ List.replicate n HStep.D

end YoungDiagramFinset
