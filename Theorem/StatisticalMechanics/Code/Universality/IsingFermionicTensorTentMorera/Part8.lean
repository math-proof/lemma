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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part6


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

theorem reflectedRadialDiscretePrimitive_succ_j
    (H V : Nat -> Nat -> Complex) (i0 j0 a b : Nat) :
    reflectedRadialDiscretePrimitive H V i0 j0 a (b + 1) -
        reflectedRadialDiscretePrimitive H V i0 j0 a b =
      V (i0 + a) (j0 + b) := by
  unfold reflectedRadialDiscretePrimitive
  rw [Finset.sum_range_succ]
  ring


theorem reflectedRadialDiscretePrimitive_succ_i
    (H V : Nat -> Nat -> Complex) (i0 j0 a b : Nat)
    (hcurl : ∀ y < b,
      H (i0 + a) (j0 + y) + V (i0 + a + 1) (j0 + y) -
        H (i0 + a) (j0 + y + 1) - V (i0 + a) (j0 + y) = 0) :
    reflectedRadialDiscretePrimitive H V i0 j0 (a + 1) b -
        reflectedRadialDiscretePrimitive H V i0 j0 a b =
      H (i0 + a) (j0 + b) := by
  have hVdiff :
      (∑ y ∈ Finset.range b, V (i0 + a + 1) (j0 + y)) -
          (∑ y ∈ Finset.range b, V (i0 + a) (j0 + y)) =
        H (i0 + a) (j0 + b) - H (i0 + a) j0 := by
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ y ∈ Finset.range b,
          (V (i0 + a + 1) (j0 + y) - V (i0 + a) (j0 + y))) =
          ∑ y ∈ Finset.range b,
            (H (i0 + a) (j0 + y + 1) - H (i0 + a) (j0 + y)) := by
        apply Finset.sum_congr rfl
        intro y hy
        have hc := hcurl y (Finset.mem_range.mp hy)
        linear_combination hc
      _ = H (i0 + a) (j0 + b) - H (i0 + a) j0 := by
        exact sum_range_add_one_sub (fun j => H (i0 + a) j) j0 b
  unfold reflectedRadialDiscretePrimitive
  rw [Finset.sum_range_succ]
  have hi : i0 + (a + 1) = i0 + a + 1 := by omega
  rw [hi]
  linear_combination hVdiff


theorem reflectedRadialDiscretePrimitive_succ_i_of_cellCR
    (mesh : Real) (F : Nat -> Nat -> Complex)
    (i0 j0 a b : Nat)
    (hCR : ∀ y < b, IsingCellCRAt F (i0 + a) (j0 + y)) :
    reflectedRadialDiscretePrimitive
          (reflectedRadialHorizontalEdgeIntegral mesh F)
          (reflectedRadialVerticalEdgeIntegral mesh F)
          i0 j0 (a + 1) b -
        reflectedRadialDiscretePrimitive
          (reflectedRadialHorizontalEdgeIntegral mesh F)
          (reflectedRadialVerticalEdgeIntegral mesh F)
          i0 j0 a b =
      reflectedRadialHorizontalEdgeIntegral mesh F
        (i0 + a) (j0 + b) := by
  apply reflectedRadialDiscretePrimitive_succ_i
  intro y hy
  rw [← reflectedRadialBilinearCellContour_eq_edgeCoboundary]
  exact reflectedRadialBilinearCellContour_eq_zero_of_cellCR mesh _ _ _ _
    (hCR y hy)


end
end StatMech.Universality
