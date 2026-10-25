/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicPlaneEmbedding.Part3
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.FK.PeriodicPlanar

noncomputable section

@[simp] theorem squareOffsetVertex_apply (offset : Complex) (x : Site 2) :
    squareOffsetVertex offset x = squareComplexPoint x + offset := rfl

theorem squareOffsetVertex_shift (offset : Complex) (z x : Site 2) :
    squareOffsetVertex offset (siteTranslate z x) =
      squareOffsetVertex offset x + squareComplexPeriod z := by
  apply Complex.ext <;> simp [siteTranslate, squareComplexPeriod] <;> ring


theorem squareOffsetVertex_proper (offset : Complex) (R : Real) :
    {x : Site 2 | ‖(squareOffsetVertex offset x : Complex)‖ ≤ R}.Finite := by
  let B : Real := |R| + ‖offset‖
  let n : Nat := ⌈B⌉₊
  apply (box_finite 2 n).subset
  intro x hx
  rw [mem_box]
  intro i
  have hnorm : ‖(squareComplexPoint x : Complex)‖ ≤ B := by
    calc
      ‖(squareComplexPoint x : Complex)‖ =
          ‖(squareOffsetVertex offset x : Complex) - offset‖ := by
            congr 1
            simp [squareOffsetVertex]
      _ ≤ ‖(squareOffsetVertex offset x : Complex)‖ + ‖offset‖ := norm_sub_le _ _
      _ ≤ |R| + ‖offset‖ := by
        simpa only [add_comm] using
          add_le_add_right (hx.trans (le_abs_self R)) ‖offset‖
      _ = B := rfl
  have hcoord : |((x i : Int) : Real)| ≤ B := by
    fin_cases i
    · simpa only [squareComplexPoint_re] using
        (Complex.abs_re_le_norm (squareComplexPoint x)).trans hnorm
    · simpa only [squareComplexPoint_im] using
        (Complex.abs_im_le_norm (squareComplexPoint x)).trans hnorm
  have hreal : ((x i).natAbs : Real) ≤ (n : Real) := by
    calc
      ((x i).natAbs : Real) = |((x i : Int) : Real)| := by
        calc
          ((x i).natAbs : Real) = (((x i).natAbs : Int) : Real) := by norm_num
          _ = ((|x i| : Int) : Real) := by rw [Int.natCast_natAbs]
          _ = |((x i : Int) : Real)| := by rw [Int.cast_abs]
      _ ≤ B := hcoord
      _ ≤ (n : Real) := Nat.le_ceil B
  exact_mod_cast hreal


end
end StatMech.FrontierD
