/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part2
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


noncomputable def pottsLabelTwistEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : Nat} [NeZero q] (root : ι) (increment : Fin q) :
    (ι -> Fin q) ≃ (ι -> Fin q) where
  toFun := pottsLabelTwist root increment
  invFun := pottsLabelTwist root (-increment)
  left_inv label := by
    funext i
    by_cases hi : i = root
    · subst i
      simp [pottsLabelTwist]
    · simp [pottsLabelTwist, hi]
  right_inv label := by
    funext i
    by_cases hi : i = root
    · subst i
      simp [pottsLabelTwist]
    · simp [pottsLabelTwist, hi]


noncomputable def pottsClusterSumFiberEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {q : Nat} [NeZero q] (a b : Fin q) :
    {label : ι -> Fin q // ∑ i, label i = a} ≃
      {label : ι -> Fin q // ∑ i, label i = b} := by
  let root : ι := Classical.choice inferInstance
  let twist := pottsLabelTwistEquiv root (b - a)
  refine
    { toFun := fun label => ⟨twist label, ?_⟩
      invFun := fun label => ⟨twist.symm label, ?_⟩
      left_inv := fun label => Subtype.ext (twist.left_inv label)
      right_inv := fun label => Subtype.ext (twist.right_inv label) }
  · change ∑ i, pottsLabelTwist root (b - a) label.1 i = b
    rw [sum_pottsLabelTwist, label.2]
    abel
  · change ∑ i, pottsLabelTwist root (-(b - a)) label.1 i = a
    rw [sum_pottsLabelTwist, label.2]
    abel


end StatMech.FK
