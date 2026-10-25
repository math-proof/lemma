/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SpinAssembly
import Theorem.StatisticalMechanics.Code.Onsager.TorusSpinSectors.Part3
import Def.StatisticalMechanics.Code.Onsager.SpinPolynomial.Part2


namespace StatMech.Onsager

open StatMech.Ising Polynomial

theorem ons_spinDet_eq_spinDetX (L : ℕ) (beta : ℝ) (a b : Fin 2) :
    ons_spinDet L beta a b = ons_spinDetX L (Real.tanh beta) a b := by
  unfold ons_spinDet ons_spinDetX ons_symbolDispersion
  rfl

end StatMech.Onsager
