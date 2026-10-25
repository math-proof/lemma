/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusSpinSectors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CoeffMatch
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Theorem.StatisticalMechanics.Code.Onsager.TorusSpinSectors


namespace StatMech.Onsager

open StatMech.Ising


noncomputable def ons_sectorWeight (L : ℕ) [Fact (2 < L)] (x : ℝ) (h : Fin 2 × Fin 2) : ℝ :=
  ∑ F ∈ evenSubgraphs (onsTorusGraph L) with ons_evenHomology L F = h, x ^ F.card

end StatMech.Onsager
