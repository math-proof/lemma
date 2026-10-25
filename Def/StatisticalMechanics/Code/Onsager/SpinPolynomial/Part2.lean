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
import Theorem.StatisticalMechanics.Code.Onsager.SpinPolynomial


namespace StatMech.Onsager

open StatMech.Ising Polynomial

noncomputable def ons_spinDetX (L : ℕ) (x : ℝ) (a b : Fin 2) : ℝ :=
  ∏ i ∈ Finset.range L, ∏ j ∈ Finset.range L,
    ((1 + x ^ 2) ^ 2 - 2 * x * (1 - x ^ 2) *
      (Real.cos (2 * Real.pi * (i + (a.val : ℝ) / 2) / L) +
        Real.cos (2 * Real.pi * (j + (b.val : ℝ) / 2) / L)))

end StatMech.Onsager
