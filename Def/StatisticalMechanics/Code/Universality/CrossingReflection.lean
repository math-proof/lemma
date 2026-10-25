/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


def crf_swapFun (x : Site 2) : Site 2 := ![x 1, x 0]


def crf_swap : Site 2 ≃ Site 2 where
  toFun := crf_swapFun
  invFun := crf_swapFun
  left_inv x := by funext i; fin_cases i <;> simp [crf_swapFun]
  right_inv x := by funext i; fin_cases i <;> simp [crf_swapFun]

end Universality
end StatMech
