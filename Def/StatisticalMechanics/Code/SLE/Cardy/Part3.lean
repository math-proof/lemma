/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
import Theorem.StatisticalMechanics.Code.SLE.Cardy.Part2
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

noncomputable def cardyPrefactor : ℝ :=
  3 * Real.Gamma (2 / 3) / (Real.Gamma (1 / 3)) ^ 2


noncomputable def cardyCrossing (s : ℝ) : ℝ :=
  cardyPrefactor * s ^ ((1 : ℝ) / 3) *
    ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3) (4 / 3) s


end StatMech.SLE
