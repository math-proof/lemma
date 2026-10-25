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
import Theorem.StatisticalMechanics.Code.Onsager.TorusSpinSectors.Part2


namespace StatMech.Onsager

open StatMech.Ising


noncomputable def ons_sector00 (L : ℕ) [Fact (2 < L)] (x : ℝ) : ℝ :=
  ons_sectorWeight L x (0, 0)

noncomputable def ons_sector10 (L : ℕ) [Fact (2 < L)] (x : ℝ) : ℝ :=
  ons_sectorWeight L x (1, 0)

noncomputable def ons_sector01 (L : ℕ) [Fact (2 < L)] (x : ℝ) : ℝ :=
  ons_sectorWeight L x (0, 1)

noncomputable def ons_sector11 (L : ℕ) [Fact (2 < L)] (x : ℝ) : ℝ :=
  ons_sectorWeight L x (1, 1)


noncomputable def ons_spin00 (L : ℕ) [Fact (2 < L)] (x : ℝ) : ℝ :=
  ons_sector00 L x + ons_sector10 L x + ons_sector01 L x - ons_sector11 L x

noncomputable def ons_spin10 (L : ℕ) [Fact (2 < L)] (x : ℝ) : ℝ :=
  ons_sector00 L x - ons_sector10 L x + ons_sector01 L x + ons_sector11 L x

noncomputable def ons_spin01 (L : ℕ) [Fact (2 < L)] (x : ℝ) : ℝ :=
  ons_sector00 L x + ons_sector10 L x - ons_sector01 L x + ons_sector11 L x

noncomputable def ons_spin11 (L : ℕ) [Fact (2 < L)] (x : ℝ) : ℝ :=
  ons_sector00 L x - ons_sector10 L x - ons_sector01 L x - ons_sector11 L x

end StatMech.Onsager
