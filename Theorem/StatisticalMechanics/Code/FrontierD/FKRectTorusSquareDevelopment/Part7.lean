/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part7


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectIntModFin_natCast {N : Nat} (hN : 0 < N)
    (i : Fin N) :
    fkRectIntModFin hN (i.val : Int) = i := by
  apply Fin.ext
  simp [fkRectIntModFin, Int.natMod, Int.emod_eq_of_lt,
    Int.natCast_nonneg, i.isLt]

@[simp] theorem fkRectIntModFin_natCast_sub_one {N : Nat} (hN : 0 < N)
    (i : Fin N) :
    fkRectIntModFin hN ((i.val : Int) - 1) =
      SixVertexArrows.cyclicPred hN i := by
  apply Fin.ext
  by_cases hi : i.val = 0
  · simp only [fkRectIntModFin, Fin.val_mk, Int.natMod,
      SixVertexArrows.cyclicPred, hi, Nat.zero_add]
    have hrepr : (-1 : Int) = ((N - 1 : Nat) : Int) + (N : Int) * (-1) := by
      omega
    have hnonneg : (0 : Int) ≤ ((N - 1 : Nat) : Int) := by omega
    have hlt : ((N - 1 : Nat) : Int) < N := by omega
    have hmod : (-1 : Int) % (N : Int) = (N - 1 : Nat) := by
      rw [hrepr, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt hnonneg hlt]
    change ((-1 : Int) % (N : Int)).toNat = (N - 1) % N
    rw [hmod, Int.toNat_natCast, Nat.mod_eq_of_lt (by omega)]
  · have hiPos : (0 : Int) <= (i.val : Int) - 1 := by omega
    have hiLt : (i.val : Int) - 1 < N := by omega
    simp only [fkRectIntModFin, Fin.val_mk, Int.natMod,
      SixVertexArrows.cyclicPred]
    rw [Int.emod_eq_of_lt hiPos hiLt]
    have htoNat : ((i.val : Int) - 1).toNat = i.val - 1 := by
      rw [← Int.natCast_inj]
      rw [Int.natCast_toNat_eq_self.mpr hiPos]
      omega
    rw [htoNat]
    rw [show i.val + N - 1 = (i.val - 1) + N by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]


end
end StatMech.FrontierD
