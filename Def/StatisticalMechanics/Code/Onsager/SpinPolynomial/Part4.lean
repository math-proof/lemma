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
import Theorem.StatisticalMechanics.Code.Onsager.SpinPolynomial.Part3


namespace StatMech.Onsager

open StatMech.Ising Polynomial

def ons_spinKacWardAt (L : ℕ) [Fact (2 < L)] (x : ℝ) : Prop :=
  ons_spin11 L x ^ 2 = ons_spinDetX L x 0 0 ∧
  ons_spin01 L x ^ 2 = ons_spinDetX L x 1 0 ∧
  ons_spin10 L x ^ 2 = ons_spinDetX L x 0 1 ∧
  ons_spin00 L x ^ 2 = ons_spinDetX L x 1 1


end StatMech.Onsager
