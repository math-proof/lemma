/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FurstenbergProposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.FurstenbergProposition


noncomputable section

open Real Set

namespace FurstenbergSets

/-- Configuration data for the Furstenberg $\delta$-tube incidence proposition: a scale
$\delta$, exponents $t$ (for $E$) and $s$ (for the direction sets), a $(\delta, t, C)$-set
$E \subset \mathbb{R}^2$, and for each $x \in E$ a $(\delta, s, C)$-set of tube directions
$\mathbb{T}_x \subset S^1$, together with a total-tube count `totalTubes` bounding
$|\mathbb{T}_x|$ uniformly. -/
structure FurstenbergConfig where
  δ : ℝ
  t : ℝ
  s : ℝ
  C : ℝ
  E : Finset (EuclideanSpace ℝ (Fin 2))
  tubeDirections : EuclideanSpace ℝ (Fin 2) → Finset ℝ
  totalTubes : ℕ
  hδ_pos : 0 < δ
  hδ_le : δ ≤ 1
  hs_pos : 0 < s
  ht_pos : 0 < t
  hC : 1 ≤ C
  hE_spacing : IsDeltaSC E δ t C
  hDir_spacing : ∀ x ∈ E, IsDeltaSC_S1 (tubeDirections x) δ s C
  hTotalTubes_lower : ∀ x ∈ E, (tubeDirections x).card ≤ totalTubes

end FurstenbergSets
end
