/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKCriticalAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace StatMech.FrontierA

def triangularFKCriticalPolynomial (q y : ℝ) : ℝ :=
  y ^ 3 + 3 * y ^ 2 - q


def hexagonalFKCriticalPolynomial (q y : ℝ) : ℝ :=
  y ^ 3 - 3 * q * y - q ^ 2


end StatMech.FrontierA
