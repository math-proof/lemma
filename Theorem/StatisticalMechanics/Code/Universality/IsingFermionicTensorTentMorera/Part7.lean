/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Def.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part5


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

theorem reflectedRadialBilinearCellContour_eq_edgeCoboundary
    (mesh : Real) (F : Nat -> Nat -> Complex) (i j : Nat) :
    reflectedRadialBilinearCellContour mesh
        (F i j) (F (i + 1) j) (F i (j + 1)) (F (i + 1) (j + 1)) =
      reflectedRadialHorizontalEdgeIntegral mesh F i j +
        reflectedRadialVerticalEdgeIntegral mesh F (i + 1) j -
        reflectedRadialHorizontalEdgeIntegral mesh F i (j + 1) -
        reflectedRadialVerticalEdgeIntegral mesh F i j := by
  unfold reflectedRadialBilinearCellContour
    reflectedRadialHorizontalEdgeIntegral reflectedRadialVerticalEdgeIntegral
  ring

theorem sum_range_add_one_sub (f : Nat -> Complex) (base n : Nat) :
    (∑ k ∈ Finset.range n, (f (base + k + 1) - f (base + k))) =
      f (base + n) - f base := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.add_succ]
      ring

theorem sum_range_sub_add_one (f : Nat -> Complex) (base n : Nat) :
    (∑ k ∈ Finset.range n, (f (base + k) - f (base + k + 1))) =
      f base - f (base + n) := by
  rw [show (∑ k ∈ Finset.range n,
      (f (base + k) - f (base + k + 1))) =
      -(∑ k ∈ Finset.range n,
        (f (base + k + 1) - f (base + k))) by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    ring]
  rw [sum_range_add_one_sub]
  ring


end
end StatMech.Universality
