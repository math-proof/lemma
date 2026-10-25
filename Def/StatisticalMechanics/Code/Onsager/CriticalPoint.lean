/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace StatMech.Onsager

open Real


noncomputable def ons_gInt (β k₁ k₂ : ℝ) : ℝ :=
  Real.cosh (2*β)^2 - Real.sinh (2*β) * (Real.cos k₁ + Real.cos k₂)


noncomputable def ons_betaC : ℝ := (1/2) * Real.log (1 + Real.sqrt 2)


end StatMech.Onsager
