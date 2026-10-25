/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice


def rss_stripReflectFun (n : ℤ) (x : Site 2) : Site 2 :=
  ![x 0 + 1, 2 * n - 1 - x 1]


def rss_stripReflectInvFun (n : ℤ) (x : Site 2) : Site 2 :=
  ![x 0 - 1, 2 * n - 1 - x 1]


def rss_stripReflect (n : ℤ) : Site 2 ≃ Site 2 where
  toFun := rss_stripReflectFun n
  invFun := rss_stripReflectInvFun n
  left_inv x := by
    ext i
    fin_cases i <;> simp [rss_stripReflectFun, rss_stripReflectInvFun]
  right_inv x := by
    ext i
    fin_cases i <;> simp [rss_stripReflectFun, rss_stripReflectInvFun]

end Universality
end StatMech
