/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/SchreierRefinement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLn.Part3
import Lemma.Nat.TypeA_CoxeterMatrixA
import Structure.v1.Atlas.Buildings.code.SphericalBuilding.SchreierRefinement


namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- The Schreier refinement cell at row $i$ and column $j$:
$\sigma_i \cap (\sigma_{i-1} + \tau_j)$, interpolating between $\sigma_{i-1}$ and $\sigma_i$
along the chain $\tau$. -/
def schreierCell (σ τ : CompleteFlag k n)
    (i : Fin (n + 1)) (hi : 0 < i.val) (j : Fin (n + 1)) : Submodule k (Vec k n) :=
  σ.spaces i ⊓ (σ.spaces ⟨i.val - 1, by omega⟩ ⊔ τ.spaces j)

end GLnBuilding
