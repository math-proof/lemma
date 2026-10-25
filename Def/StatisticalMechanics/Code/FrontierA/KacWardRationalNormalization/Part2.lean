/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalPhaseReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization


namespace StatMech.FrontierA

open scoped BigOperators


def kwIntComplex (p : ℤ × ℤ) : ℂ :=
  (p.1 : ℝ) + (p.2 : ℝ) * Complex.I


end StatMech.FrontierA
