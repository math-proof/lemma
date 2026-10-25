/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/MoserCorrectness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.MoserCorrectness.Part2
set_option maxHeartbeats 400000

open Finset


namespace MoserCorrectness

/-- Bundle produced by the entropy-compression argument: a set of "failing" random strings of size at most $2^n \cdot 2^{\ell(k-1)+1}$, together with a proof that any string outside this set witnesses satisfiability of $\varphi$. -/
structure EntropyCompression (n m k ℓ : ℕ) (φ : KCNF n m k) where
  failingStrings : Finset (Fin (2 ^ (k * ℓ)))
  card_bound : failingStrings.card ≤ 2 ^ n * 2 ^ (ℓ * (k - 1) + 1)
  success_implies_sat : ∀ x : Fin (2 ^ (k * ℓ)), x ∉ failingStrings → φ.satisfiable

end MoserCorrectness
