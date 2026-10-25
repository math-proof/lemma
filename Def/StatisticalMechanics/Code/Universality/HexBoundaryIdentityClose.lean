/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryIdentityClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConnFinal


namespace StatMech.Universality

open Complex Filter Topology

open scoped Real BigOperators Topology


noncomputable def hbi_sigma : ℝ := 5 / 8


noncomputable def hbi_j : ℂ := Complex.exp ((2 * Real.pi / 3 : ℝ) * Complex.I)


end StatMech.Universality
