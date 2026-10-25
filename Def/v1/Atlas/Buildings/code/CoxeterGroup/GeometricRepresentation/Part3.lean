/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part3
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation.Part3
open Finset BigOperators


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- Action of a word $s_1 \cdots s_k$ on $\mathbb{R}^B$ by the composition of geometric
reflections $\sigma_{s_1} \circ \cdots \circ \sigma_{s_k}$. -/
noncomputable def wordSigma (M : CoxeterMatrix B) : List B → (B → ℝ) → (B → ℝ)
  | [], v => v
  | s :: rest, v => sigma M s (wordSigma M rest v)

end CoxeterGroup
