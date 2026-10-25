/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part3


namespace StatMech.Universality

open Complex


noncomputable def hexContribution (dir : ℂ) (k : ℤ) (n : ℕ) : ℂ :=
  dir * hexLambda ^ k * (hexChi : ℂ) ^ n


end StatMech.Universality
