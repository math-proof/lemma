/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DilatedSumsetExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.ProjectionTheory.code.PolyKGrowth
import Lemma.Real.Atlas.v1.ProjectionTheory.code.ContagiousStructure
import Def.v1.Atlas.ProjectionTheory.code.DoubleCountingFF
import Lemma.Real.Atlas.v1.ProjectionTheory.code.DoubleCountingFF
open Pointwise


namespace ProjectionTheory

/--
Contagious-structure lower bound underlying the dilated sumset expansion. For
exponents `0 < s_A < 1` and `0 < s_D`, there exist `r, c > 0` such that for any
prime `p`, any `A, D ⊆ 𝔽_p` with `|A| = p^{s_A}` and `|D| = p^{s_D}`, and any
`K ≥ 1` with `|A + t·A| ≤ K|A|` for all `t ∈ D`, one has `K^c ≥ p^r`. That is,
small dilated sumsets across a sufficiently large set of directions force `K`
itself to grow like a power of `p`.
-/
noncomputable def sumProductSet {p : ℕ} [Fact (Nat.Prime p)]
    (A : Finset (ZMod p)) : Finset (ZMod p) :=
  A.biUnion (fun a => A.biUnion (fun b => A.image (fun c => a + b * c)))

end ProjectionTheory
