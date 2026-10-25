/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnicyclicAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardCycleAssembly.Part3
open scoped BigOperators


namespace StatMech.FrontierA

open Matrix


theorem kw_det_one_sub_blockTriangular
    {D Block : Type*} [Fintype D] [DecidableEq D]
    [Fintype Block] [DecidableEq Block] [LinearOrder Block]
    (transition : Matrix D D ℂ) (block : D -> Block)
    (htriangular : transition.BlockTriangular block) :
    (1 - transition).det =
      ∏ k : Block, (1 - transition.toSquareBlock block k).det := by
  have honeSub : (1 - transition).BlockTriangular block :=
    Matrix.blockTriangular_one.sub htriangular
  rw [honeSub.det_fintype]
  apply Finset.prod_congr rfl
  intro k _
  congr 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.toSquareBlock_def, Matrix.of_apply]
  by_cases hij : i = j
  · subst j
    simp
  · have hval : (i : D) ≠ (j : D) := fun h => hij (Subtype.ext h)
    simp [hij, hval]


end StatMech.FrontierA
