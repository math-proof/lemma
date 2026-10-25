/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCactusAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnicyclicAssembly.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open Matrix


noncomputable def kwCycleFamilyDiagonal
    {E Block : Type*} [Fintype E] [DecidableEq E]
    [Fintype Block] [DecidableEq Block]
    (sigma : Block -> Equiv.Perm E)
    (weight : Block -> Bool -> E -> ℂ) :
    Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ :=
  Matrix.blockDiagonal fun b =>
    kwTwoOrientationCycleTransition (sigma b) (weight b)


noncomputable def kwCycleFamilyExtension
    {E Block : Type*} [Fintype E] [DecidableEq E]
    [Fintype Block] [DecidableEq Block]
    (sigma : Block -> Equiv.Perm E)
    (weight : Block -> Bool -> E -> ℂ)
    (forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ) :
    Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ :=
  kwCycleFamilyDiagonal sigma weight + forward


def kwCycleBlockEquiv {E Block : Type*} (b : Block) :
    {d : (E × Bool) × Block // d.2 = b} ≃ (E × Bool) where
  toFun d := d.1.1
  invFun d := ⟨(d, b), rfl⟩
  left_inv d := by
    apply Subtype.ext
    exact Prod.ext rfl d.property.symm
  right_inv d := rfl


def kwStrictlyForward
    {E Block : Type*} [LT Block]
    (forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ) : Prop :=
  ∀ i j, forward i j ≠ 0 -> i.2 < j.2


end StatMech.FrontierA
