/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralSharp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Theorem.StatisticalMechanics.Code.Onsager.KWSpectral.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
import Theorem.StatisticalMechanics.Code.Onsager.KWSpectralSharp.Part2


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


def ons_headDartEquiv (L : ℕ) : Equiv.Perm (ons_Dart L) where
  toFun d := (ons_dirStep L d.2 d.1, d.2)
  invFun d := (ons_dirStep L (d.2 + 2) d.1, d.2)
  left_inv d := by
    apply Prod.ext
    · exact ons_dirStep_opposite L d.2 d.1
    · rfl
  right_inv d := by
    rcases d with ⟨p, mu⟩
    fin_cases mu <;> simp [ons_dirStep]

def ons_tailDartEquiv (L : ℕ) : Equiv.Perm (ons_Dart L) :=
  (ons_headDartEquiv L).symm

end StatMech.Onsager
