/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
import Theorem.StatisticalMechanics.Code.Onsager.KWSpinFourier.Part3
import Theorem.StatisticalMechanics.Code.Onsager.Pressure.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TorusSpinSectors.Part3


namespace StatMech.Onsager

open StatMech.Ising


def ons_spinKacWardIdentities (beta : ℝ) : Prop :=
  ∀ (L : ℕ) (hL : 2 < L),
    letI : Fact (2 < L) := ⟨hL⟩
    ons_spin11 L (Real.tanh beta) ^ 2 = ons_spinDet L beta 0 0 ∧
    ons_spin01 L (Real.tanh beta) ^ 2 = ons_spinDet L beta 1 0 ∧
    ons_spin10 L (Real.tanh beta) ^ 2 = ons_spinDet L beta 0 1 ∧
    ons_spin00 L (Real.tanh beta) ^ 2 = ons_spinDet L beta 1 1


def ons_spinKacWardMatrixIdentities (beta : ℝ) : Prop :=
  ∀ (L : ℕ) (hL : 2 < L),
    letI : Fact (2 < L) := ⟨hL⟩
    ((ons_spin11 L (Real.tanh beta) : ℂ) ^ 2 =
      (1 - ons_KWmatPhase L (Real.tanh beta : ℂ) ons_turnRoot
        (ons_spinPhase L 0) (ons_spinPhase L 0)).det) ∧
    ((ons_spin01 L (Real.tanh beta) : ℂ) ^ 2 =
      (1 - ons_KWmatPhase L (Real.tanh beta : ℂ) ons_turnRoot
        (ons_spinPhase L 1) (ons_spinPhase L 0)).det) ∧
    ((ons_spin10 L (Real.tanh beta) : ℂ) ^ 2 =
      (1 - ons_KWmatPhase L (Real.tanh beta : ℂ) ons_turnRoot
        (ons_spinPhase L 0) (ons_spinPhase L 1)).det) ∧
    ((ons_spin00 L (Real.tanh beta) : ℂ) ^ 2 =
      (1 - ons_KWmatPhase L (Real.tanh beta : ℂ) ons_turnRoot
        (ons_spinPhase L 1) (ons_spinPhase L 1)).det)

end StatMech.Onsager
