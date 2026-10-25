/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3


namespace StatMech.Universality

open Complex

open scoped BigOperators


noncomputable def hexPhase_sideTilt (h : ℤ) : ℝ := (1 - (h : ℝ)) * (Real.pi / 3)


end StatMech.Universality
