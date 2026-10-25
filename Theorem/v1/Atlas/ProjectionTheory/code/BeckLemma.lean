/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BeckLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.BourgainLemma.Part2
/-- **ε-bootstrap step for Continuum Beck's Theorem.** If `0 < s < min(u, 1)` then
there exist `ε > 0` and `η ∈ (0, 1)` such that the following holds: for any scale
`Δ ∈ (0, 1)`, any `m`, any planar set `E` with a uniform "good" subset `G ⊆ E` of
proportional `Δ^m`-mesh count at least `1 − η`, where each `Lx` (the line-set through
`x ∈ G`) is `(Δ^m, s, C)`-regular, one can produce a possibly smaller good set
`G' ⊆ E` of the same proportional size on which the line-set is `(Δ^m, s + ε, C')`-
regular. This is the bootstrap mechanism behind the lemma "if a typical `L_{x,E}` is
`(δ, s, C)` then a typical `L_{x,E}` is `(δ, s + ε, C')`". -/


namespace BeckLemma

open BourgainUniform

end BeckLemma

noncomputable section

open scoped NNReal ENNReal

end
