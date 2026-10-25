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
import Theorem.StatisticalMechanics.Code.Onsager.SpinPolynomial.Part2


namespace StatMech.Onsager

open StatMech.Ising Polynomial

noncomputable def ons_spinDetPoly (L : ℕ) (a b : Fin 2) : Polynomial ℝ :=
  ∏ i ∈ Finset.range L, ∏ j ∈ Finset.range L,
    ((1 + X ^ 2) ^ 2 -
      C (2 * (Real.cos (2 * Real.pi * (i + (a.val : ℝ) / 2) / L) +
        Real.cos (2 * Real.pi * (j + (b.val : ℝ) / 2) / L))) * X * (1 - X ^ 2))

end StatMech.Onsager
