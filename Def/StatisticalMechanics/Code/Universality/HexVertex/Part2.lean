/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part2


namespace StatMech.Universality

open Complex


noncomputable def hexLambda : ℂ := Complex.exp ((-(5 * Real.pi / 24) : ℝ) * Complex.I)


noncomputable def hexChi : ℝ := 1 / (2 * Real.cos (Real.pi / 8))


end StatMech.Universality
