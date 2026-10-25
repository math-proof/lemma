/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetGauge
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismGeometry


namespace StatMech.FrontierA

open StatMech Lattice Sharpness


def finOddEquivCenteredInt (n : Nat) : Fin (2 * n + 1) ≃ CenteredInt n where
  toFun i := ⟨(i.val : Int) - n, by
    have hi := i.isLt
    omega⟩
  invFun z := ⟨(z.1 + n).toNat, by
    have hzLower : -(n : Int) <= z.1 := by
      have := z.2
      omega
    have hzUpper : z.1 <= n := by
      have := z.2
      omega
    have hnonneg : 0 <= z.1 + n := by omega
    have hcast : ((z.1 + n).toNat : Int) = z.1 + n :=
      Int.toNat_of_nonneg hnonneg
    omega⟩
  left_inv i := by
    apply Fin.ext
    change (((i.val : Int) - n + n).toNat) = i.val
    rw [sub_add_cancel]
    exact Int.toNat_natCast i.val
  right_inv z := by
    apply Subtype.ext
    change ((((z.1 + n).toNat : Nat) : Int) - n) = z.1
    have hzLower : -(n : Int) <= z.1 := by
      have := z.2
      omega
    rw [Int.toNat_of_nonneg (by omega : 0 <= z.1 + n)]
    ring

end StatMech.FrontierA
