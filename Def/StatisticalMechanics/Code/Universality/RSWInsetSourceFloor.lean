/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment.Part3
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_affineFlipYFun (k : Int) (x : Site 2) : Site 2 :=
  ![x 0, k - x 1]

def rlc_affineFlipY (k : Int) : Site 2 ≃ Site 2 where
  toFun := rlc_affineFlipYFun k
  invFun := rlc_affineFlipYFun k
  left_inv x := by funext i; fin_cases i <;> simp [rlc_affineFlipYFun]
  right_inv x := by funext i; fin_cases i <;> simp [rlc_affineFlipYFun]

end
end StatMech.Universality
