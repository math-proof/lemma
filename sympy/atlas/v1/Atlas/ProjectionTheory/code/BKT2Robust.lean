/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BKT2Robust.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace BourgainKatzTaoRobust

/-- **Bourgain–Katz–Tao 2 (robust version).** With the same setup as BKT (`X ⊂ 𝔽_p²`
of size `p^{s_X}`, `D ⊂ 𝔽_p` of size `p^{s_D}` with `0 < s_X < 2`, `0 < s_D`), there
exists `ε = ε(s_X, s_D) > 0` and a direction `t ∈ D` such that the projection
`π_t : (x₁, x₂) ↦ x₁ + t·x₂` is robust: for every `Y ⊆ X` with `|Y| ≥ p^{-ε} |X|`,
`|π_t(Y)| ≥ p^ε |X|^{1/2}`. -/
end BourgainKatzTaoRobust
