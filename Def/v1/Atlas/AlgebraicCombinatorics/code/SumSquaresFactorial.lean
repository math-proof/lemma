module
public import Instance.v1.Atlas.AlgebraicCombinatorics.code.HasseWalkFormula.Part2
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.HasseWalkFormula
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkTypeCount
public import Def.v1.Atlas.AlgebraicCombinatorics.code.WalkTypeCount
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Theorem.v1.Atlas.AlgebraicCombinatorics.code.SumSquaresFactorial
set_option autoImplicit false
open scoped Nat
open HasseWalkFormula HasseWalks


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
section YoungDiagramFinset

noncomputable def youngDiagramsOfSize (n : ℕ) : Finset YoungDiagram :=
  (finite_youngDiagrams_of_size n).toFinset

def dnUn (n : ℕ) : List HStep :=
  List.replicate n HStep.U ++ List.replicate n HStep.D

end YoungDiagramFinset
