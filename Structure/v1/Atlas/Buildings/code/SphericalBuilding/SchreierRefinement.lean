/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/SchreierRefinement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLn.Part3
import Lemma.Nat.TypeA_CoxeterMatrixA


namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

structure CompleteFlag (k : Type*) [Field k] (n : ℕ) where
  spaces : Fin (n + 1) → Submodule k (Vec k n)
  monotone : Monotone spaces
  bot_eq : spaces ⟨0, Nat.zero_lt_succ n⟩ = ⊥
  top_eq : spaces ⟨n, Nat.lt_succ_of_le le_rfl⟩ = ⊤

end GLnBuilding
