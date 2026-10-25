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


namespace StatMech.Onsager

open StatMech.Ising Polynomial

noncomputable def ons_sectorPoly (L : ℕ) [Fact (2 < L)]
    (h : Fin 2 × Fin 2) : Polynomial ℝ :=
  ∑ F ∈ evenSubgraphs (onsTorusGraph L) with ons_evenHomology L F = h,
    X ^ F.card

noncomputable def ons_spinPoly00 (L : ℕ) [Fact (2 < L)] : Polynomial ℝ :=
  ons_sectorPoly L (0, 0) + ons_sectorPoly L (1, 0) +
    ons_sectorPoly L (0, 1) - ons_sectorPoly L (1, 1)

noncomputable def ons_spinPoly10 (L : ℕ) [Fact (2 < L)] : Polynomial ℝ :=
  ons_sectorPoly L (0, 0) - ons_sectorPoly L (1, 0) +
    ons_sectorPoly L (0, 1) + ons_sectorPoly L (1, 1)

noncomputable def ons_spinPoly01 (L : ℕ) [Fact (2 < L)] : Polynomial ℝ :=
  ons_sectorPoly L (0, 0) + ons_sectorPoly L (1, 0) -
    ons_sectorPoly L (0, 1) + ons_sectorPoly L (1, 1)

noncomputable def ons_spinPoly11 (L : ℕ) [Fact (2 < L)] : Polynomial ℝ :=
  ons_sectorPoly L (0, 0) - ons_sectorPoly L (1, 0) -
    ons_sectorPoly L (0, 1) - ons_sectorPoly L (1, 1)

end StatMech.Onsager
