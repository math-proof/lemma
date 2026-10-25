/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Theorem.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part8


namespace StatMech.Onsager

noncomputable def ons_gIntComplex (z : ℂ) (k1 k2 : ℝ) : ℂ :=
  Complex.cosh (2 * z) ^ 2 -
    Complex.sinh (2 * z) * ((Real.cos k1 : ℂ) + (Real.cos k2 : ℂ))

noncomputable def ons_gIntComplexDeriv (z : ℂ) (k1 k2 : ℝ) : ℂ :=
  2 * Complex.cosh (2 * z) *
    (2 * Complex.sinh (2 * z) - (Real.cos k1 : ℂ) - (Real.cos k2 : ℂ))

end StatMech.Onsager
