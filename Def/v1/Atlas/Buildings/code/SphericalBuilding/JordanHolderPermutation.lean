/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.RefinementDimJumps
import Lemma.Fin.FinrankKSpacesValAdd1.of.IsStrictFlag
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.JordanHolderPermutation
set_option maxHeartbeats 800000


namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- The **Schreier refinement permutation**: for each row $i$, `jumpCol` returns the unique
column $j$ where the refinement increases in dimension, giving the bijection between the
composition factors of $\sigma$ and those of $\tau$. -/
noncomputable def jumpCol (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) : Fin n :=
  (existsUnique_jump_col σ τ hσ hτ i hi).exists.choose

end GLnBuilding
