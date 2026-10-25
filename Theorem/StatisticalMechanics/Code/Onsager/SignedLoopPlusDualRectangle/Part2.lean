/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualRectangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualContour.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle.Part3
open Finset SimpleGraph Set


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

noncomputable section

theorem ons_plusDualCoordEquiv_dist
    (n : Nat) (x y : {z : Int // -(n : Int) - 1 <= z ∧ z <= n}) :
    Nat.dist (ons_plusDualCoordEquiv n x).val
        (ons_plusDualCoordEquiv n y).val = (x.1 - y.1).natAbs := by
  change Nat.dist (x.1 + n + 1).toNat (y.1 + n + 1).toNat = _
  have hxnat := Int.toNat_of_nonneg (by omega : 0 <= x.1 + n + 1)
  have hynat := Int.toNat_of_nonneg (by omega : 0 <= y.1 + n + 1)
  rcases Int.natAbs_eq (x.1 - y.1) with h | h
  · by_cases hxy : (x.1 + n + 1).toNat <= (y.1 + n + 1).toNat
    · rw [Nat.dist_eq_sub_of_le hxy]
      omega
    · rw [Nat.dist_comm,
        Nat.dist_eq_sub_of_le (by omega :
          (y.1 + n + 1).toNat <= (x.1 + n + 1).toNat)]
      omega
  · by_cases hxy : (x.1 + n + 1).toNat <= (y.1 + n + 1).toNat
    · rw [Nat.dist_eq_sub_of_le hxy]
      omega
    · rw [Nat.dist_comm,
        Nat.dist_eq_sub_of_le (by omega :
          (y.1 + n + 1).toNat <= (x.1 + n + 1).toNat)]
      omega


theorem ons_plusDualFaceEquivRect_adj (n : Nat)
    (f g : ons_PlusDualFaceVertex n) :
    (ons_plusDualFaceGraph n).Adj f g ↔
      (ons_rectDualGraph (2 * n + 1) (2 * n + 1)).Adj
        (ons_plusDualFaceEquivRect n f) (ons_plusDualFaceEquivRect n g) := by
  rw [show (ons_plusDualFaceGraph n).Adj f g ↔
      (f.1 0 - g.1 0).natAbs + (f.1 1 - g.1 1).natAbs = 1 by
    simp [ons_plusDualFaceGraph, hypercubicLattice_adj, Fin.sum_univ_two]]
  rw [show (ons_rectDualGraph (2 * n + 1) (2 * n + 1)).Adj
      (ons_plusDualFaceEquivRect n f) (ons_plusDualFaceEquivRect n g) ↔
      (f.1 1 = g.1 1 ∧ (f.1 0 - g.1 0).natAbs = 1) ∨
      (f.1 0 = g.1 0 ∧ (f.1 1 - g.1 1).natAbs = 1) by
    change
      ((ons_plusDualCoordEquiv n ⟨f.1 1, f.2 1⟩ =
          ons_plusDualCoordEquiv n ⟨g.1 1, g.2 1⟩ ∧
        Nat.dist (ons_plusDualCoordEquiv n ⟨f.1 0, f.2 0⟩).val
          (ons_plusDualCoordEquiv n ⟨g.1 0, g.2 0⟩).val = 1) ∨
       (ons_plusDualCoordEquiv n ⟨f.1 0, f.2 0⟩ =
          ons_plusDualCoordEquiv n ⟨g.1 0, g.2 0⟩ ∧
        Nat.dist (ons_plusDualCoordEquiv n ⟨f.1 1, f.2 1⟩).val
          (ons_plusDualCoordEquiv n ⟨g.1 1, g.2 1⟩).val = 1)) ↔ _
    rw [ons_plusDualCoordEquiv_dist n ⟨f.1 0, f.2 0⟩ ⟨g.1 0, g.2 0⟩,
      ons_plusDualCoordEquiv_dist n ⟨f.1 1, f.2 1⟩ ⟨g.1 1, g.2 1⟩]
    simp only [Equiv.apply_eq_iff_eq, Subtype.mk.injEq]]
  omega

end
end StatMech.Onsager
