/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Unitary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.SL2Representations.Part2
import Lemma.Complex.IsIsomorphicGK.of.IsIsomorphicGK.IsIsomorphicGK
import Def.v1.Atlas.LieGroups.code.SL2Unitary
set_option maxHeartbeats 800000


noncomputable section

open Complex

inductive SL2UnitaryIrred where
  | discreteSeriesPlus (m : ℕ) (hm : m ≥ 1)
  | discreteSeriesMinus (m : ℕ) (hm : m ≥ 1)
  | unitaryPrincipalSeries (t : ℝ) (ε : ZMod 2) (hirred : t ≠ 0 ∨ ε = 0)
  | complementarySeries (s : ℝ) (hs_ne : s ≠ 0) (hs_sq : s ^ 2 < 1)
  | trivial

end
