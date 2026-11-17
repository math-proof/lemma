/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexVertex

@[expose] public section

namespace StatMech.Universality

open Complex


noncomputable def hexOmega : ℂ := Complex.exp ((2 * Real.pi / 3 : ℝ) * Complex.I)


end StatMech.Universality
