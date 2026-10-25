/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCactusAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnicyclicAssembly.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardCactusAssembly
open scoped BigOperators


namespace StatMech.FrontierA

open Matrix


theorem kwStrictlyForward.blockTriangular
    {E Block : Type*} [Preorder Block]
    {forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ}
    (hforward : kwStrictlyForward forward) :
    forward.BlockTriangular Prod.snd := by
  intro i j hji
  by_contra hne
  exact (not_le_of_gt (hforward i j hne)) hji.le


theorem kwStrictlyForward.eq_zero_of_same_block
    {E Block : Type*} [Preorder Block]
    {forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ}
    (hforward : kwStrictlyForward forward)
    {i j : (E × Bool) × Block} (hij : i.2 = j.2) :
    forward i j = 0 := by
  by_contra hne
  exact (hforward i j hne).ne (by simpa using hij)


theorem kw_cycleFamily_diagonalBlock
    {E Block : Type*} [Fintype E] [DecidableEq E]
    [Fintype Block] [DecidableEq Block] [LinearOrder Block]
    (sigma : Block -> Equiv.Perm E)
    (weight : Block -> Bool -> E -> ℂ)
    (forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ)
    (hforward : kwStrictlyForward forward) (b : Block) :
    Matrix.reindex (kwCycleBlockEquiv b) (kwCycleBlockEquiv b)
        ((kwCycleFamilyExtension sigma weight forward).toSquareBlock Prod.snd b) =
      kwTwoOrientationCycleTransition (sigma b) (weight b) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.toSquareBlock_def]
  change kwCycleFamilyExtension sigma weight forward (i, b) (j, b) = _
  have hz : forward (i, b) (j, b) = 0 :=
    hforward.eq_zero_of_same_block (i := (i, b)) (j := (j, b)) rfl
  rw [kwCycleFamilyExtension, Matrix.add_apply, hz, add_zero]
  exact Matrix.blockDiagonal_apply_eq _ _ _ b


theorem kw_det_cycleFamilyExtension
    {E Block : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
    [Fintype Block] [DecidableEq Block] [LinearOrder Block]
    (sigma : Block -> Equiv.Perm E)
    (weight : Block -> Bool -> E -> ℂ)
    (forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ)
    (hforward : kwStrictlyForward forward) :
    (1 - kwCycleFamilyExtension sigma weight forward).det =
      ∏ b : Block, (1 - kwTwoOrientationCycleTransition (sigma b) (weight b)).det := by
  have htriangular :
      (kwCycleFamilyExtension sigma weight forward).BlockTriangular Prod.snd :=
    (Matrix.blockTriangular_blockDiagonal _).add hforward.blockTriangular
  rw [kw_det_one_sub_blockTriangular _ _ htriangular]
  apply Finset.prod_congr rfl
  intro b _
  rw [<- Matrix.det_reindex_self (kwCycleBlockEquiv b)]
  congr 1
  ext i j
  have hblock := congrFun (congrFun
    (kw_cycleFamily_diagonalBlock sigma weight forward hforward b) i) j
  change (kwCycleFamilyExtension sigma weight forward).toSquareBlock Prod.snd b
    ((kwCycleBlockEquiv b).symm i) ((kwCycleBlockEquiv b).symm j) = _ at hblock
  change (1 - (kwCycleFamilyExtension sigma weight forward).toSquareBlock Prod.snd b)
    ((kwCycleBlockEquiv b).symm i) ((kwCycleBlockEquiv b).symm j) = _
  rw [Matrix.sub_apply]
  rw [hblock]
  simp [Matrix.one_apply]


end StatMech.FrontierA
