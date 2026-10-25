/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideCrossing
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part2
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRowReflection_even_iff (R : FKRectTorus) (center : Nat)
    (y : Fin R.height) :
    Even (fkRectRowReflection R center y).val ↔ Even y.val := by
  rw [fkRectRowReflection_val, Even.mod_even_iff R.height_even,
    Nat.even_sub (by omega)]
  have hA : Even (2 * center + R.height) :=
    (even_two_mul center).add R.height_even
  simp [hA]

theorem fkRectRowReflection_cast (R : FKRectTorus) (center : Nat)
    (y : Fin R.height) :
    ((fkRectRowReflection R center y).val : ZMod R.height) =
      (2 * center : ZMod R.height) - y.val := by
  simp [fkRectRowReflection]
  rw [Nat.cast_sub (by omega : y.val <= 2 * center + R.height)]
  simp

theorem fkRectIntModFin_cast {N : Nat} (hN : 0 < N) (z : Int) :
    ((fkRectIntModFin hN z).val : ZMod N) = z := by
  simp only [fkRectIntModFin, Fin.val_mk]
  have hN0 : (N : Int) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hnonneg : 0 <= z % (N : Int) := Int.emod_nonneg z hN0
  have hzmod : ((z.natMod N : Nat) : Int) = z % (N : Int) := by
    simp [Int.natMod, Int.natCast_toNat_eq_self.mpr hnonneg]
  calc
    ((z.natMod N : Nat) : ZMod N) =
        (((z.natMod N : Nat) : Int) : ZMod N) := by norm_num
    _ = ((z % (N : Int) : Int) : ZMod N) := by rw [hzmod]
    _ = (z : ZMod N) := by simp

theorem fkRectRowReflection_intModFin (R : FKRectTorus) (center : Nat)
    (z : Int) :
    fkRectRowReflection R center (fkRectIntModFin R.height_pos z) =
      fkRectIntModFin R.height_pos (2 * (center : Int) - z) := by
  apply Fin.ext
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ R.height).mp
    calc
      ((fkRectRowReflection R center
          (fkRectIntModFin R.height_pos z)).val : ZMod R.height) =
          (2 * center : ZMod R.height) -
            (fkRectIntModFin R.height_pos z).val :=
        fkRectRowReflection_cast R center _
      _ = (2 * (center : Int) - z : Int) := by
        rw [fkRectIntModFin_cast]
        push_cast
        rfl
      _ = ((fkRectIntModFin R.height_pos
          (2 * (center : Int) - z)).val : ZMod R.height) := by
        rw [fkRectIntModFin_cast]
  · exact (fkRectRowReflection R center
      (fkRectIntModFin R.height_pos z)).isLt
  · exact (fkRectIntModFin R.height_pos
      (2 * (center : Int) - z)).isLt

theorem fkRectRowReflection_cyclicPred (R : FKRectTorus) (center : Nat)
    (y : Fin R.height) :
    fkRectRowReflection R center
        (SixVertexArrows.cyclicPred R.height_pos y) =
      finitePeriodicSucc R.height_pos (fkRectRowReflection R center y) := by
  have hH := R.height_pos
  apply Fin.ext
  simp only [fkRectRowReflection, fkRectCyclicPred_val,
    finitePeriodicSucc, Fin.val_mk]
  split <;> rename_i hzero
  · have hy0 : y.val = 0 := hzero
    simp only [hy0, Nat.sub_zero]
    rw [Nat.mod_add_mod]
    rw [show 2 * center + R.height - (R.height - 1) =
        2 * center + 1 by omega]
    rw [show 2 * center + R.height + 1 =
        (2 * center + 1) + R.height by omega,
      Nat.add_mod_right]
  · have hypos : 0 < y.val := Nat.pos_of_ne_zero hzero
    rw [Nat.mod_add_mod]
    congr 1
    omega

theorem fkRectRowReflection_succ_cyclicPred (R : FKRectTorus)
    (center : Nat) (y : Fin R.height) :
    SixVertexArrows.cyclicPred R.height_pos
        (finitePeriodicSucc R.height_pos
          (fkRectRowReflection R center y)) =
      fkRectRowReflection R center y := by
  have h := finitePeriodicSucc_cyclicPred R.height_pos
    (finitePeriodicSucc R.height_pos (fkRectRowReflection R center y))
  apply (svFinitePeriodicSuccEquiv R.height_pos).injective
  simpa using h


end
end StatMech.FrontierD
