/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BKTTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.ProjectionTheory.code.BKTLemma4
/-- Structured-subset version of BKT: assuming `X ⊆ A × A` for some `A ⊆ 𝔽_p` with
`|A|² ≥ |X|`, there exist `ε > 0` and a direction `t ∈ D` so that the projection
`π_t(X) = {x₁ + t · x₂ : x ∈ X}` satisfies `|π_t(X)| ≥ p^ε · |X|^{1/2}`. This is the
key step in deducing BKT from the abelian sum–product input. -/


namespace BKT

open Finset

end BKT
