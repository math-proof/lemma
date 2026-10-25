/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopThermodynamicLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopThermodynamicLimit
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Sharpness StatMech.FrontierA
  StatMech.FrontierB

noncomputable section

noncomputable def ons_centeredCoordEquiv (n : Nat) :
    {z : Int // z.natAbs <= n} ≃ Fin (2 * n + 1) where
  toFun z := ⟨(z.1 + n).toNat, by
    have hz := ons_int_bounds_of_natAbs_le z.2
    omega⟩
  invFun k := ⟨(k : Int) - n, by
    have hk := k.2
    have hb : -(n : Int) <= (k : Int) - n ∧ (k : Int) - n <= n := by
      constructor <;> omega
    rcases Int.natAbs_eq ((k : Int) - n) with h | h <;> omega⟩
  left_inv z := by
    apply Subtype.ext
    have hz := ons_int_bounds_of_natAbs_le z.2
    simp only
    rw [Int.toNat_of_nonneg (by omega : 0 <= z.1 + n)]
    omega
  right_inv k := by
    apply Fin.ext
    simp only
    have hk := k.2
    rw [show (k : Int) - n + n = (k : Int) by ring]
    exact Int.toNat_natCast k


noncomputable def ons_box2EquivRect (n : Nat) :
    sctBox 2 n ≃ ons_RectDualVertex (2 * n) (2 * n) where
  toFun x :=
    (ons_centeredCoordEquiv n ⟨x.1 0, x.2 0⟩,
      ons_centeredCoordEquiv n ⟨x.1 1, x.2 1⟩)
  invFun x :=
    ⟨![((ons_centeredCoordEquiv n).symm x.1).1,
        ((ons_centeredCoordEquiv n).symm x.2).1], by
      intro i
      fin_cases i
      · exact ((ons_centeredCoordEquiv n).symm x.1).2
      · exact ((ons_centeredCoordEquiv n).symm x.2).2⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    fin_cases i
    · exact congrArg Subtype.val
        ((ons_centeredCoordEquiv n).symm_apply_apply
          ⟨x.1 0, x.2 0⟩)
    · exact congrArg Subtype.val
        ((ons_centeredCoordEquiv n).symm_apply_apply
          ⟨x.1 1, x.2 1⟩)
  right_inv x := by
    apply Prod.ext <;>
      exact (ons_centeredCoordEquiv n).apply_symm_apply _

end
end StatMech.Onsager
