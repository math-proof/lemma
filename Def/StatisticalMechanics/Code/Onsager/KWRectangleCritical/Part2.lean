/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.KWSpectralCritical
import Instance.StatisticalMechanics.Code.Onsager.KWRectangleCritical


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


noncomputable def ons_rectDartMask (M N : Nat) :
    Matrix (ons_RectDart M N) (ons_RectDart M N) Complex :=
  Matrix.diagonal fun d => if ons_rectDartValid M N d then 1 else 0


def ons_rectHeadDartEquiv (M N : Nat) : Equiv.Perm (ons_RectDart M N) where
  toFun d := (ons_rectDirStep M N d.2 d.1, d.2)
  invFun d := (ons_rectDirStep M N (d.2 + 2) d.1, d.2)
  left_inv d := by
    apply Prod.ext
    · rcases d with ⟨p, mu⟩
      fin_cases mu <;> simp [ons_rectDirStep]
    · rfl
  right_inv d := by
    apply Prod.ext
    · rcases d with ⟨p, mu⟩
      fin_cases mu <;> simp [ons_rectDirStep]
    · rfl


def ons_rectTailDartEquiv (M N : Nat) : Equiv.Perm (ons_RectDart M N) :=
  (ons_rectHeadDartEquiv M N).symm

end StatMech.Onsager
