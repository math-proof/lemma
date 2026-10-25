/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.FreeEnergy
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Theorem.StatisticalMechanics.Code.Onsager.CriticalTransfer


namespace StatMech.Onsager

open StatMech.Ising

noncomputable def ons_torusPressureSeq (beta : ℝ) (L : ℕ) : ℝ :=
  if h : 2 < L then
    letI : Fact (2 < L) := ⟨h⟩
    ons_pressureFinite (onsTorusGraph L) beta
  else 0

end StatMech.Onsager
