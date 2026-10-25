/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.RefinementDimJumps
import Lemma.Fin.FinrankKSpacesValAdd1.of.IsStrictFlag
import Def.v1.Atlas.Buildings.code.SphericalBuilding.JordanHolderPermutation.Part2
set_option maxHeartbeats 800000


namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- The Jordan-Hölder gap vector lies in $V_i \cap W_{j+1}$. -/
theorem jhGapVector_mem_inf (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    jhGapVector σ τ hσ hτ i hi ∈
      σ.spaces i ⊓ τ.spaces ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ :=
  (exists_jhGapVector σ τ hσ hτ i hi).choose_spec.1

/-- The Jordan-Hölder gap vector does not lie in $V_{i-1}$. -/
theorem jhGapVector_not_mem_lower (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    jhGapVector σ τ hσ hτ i hi ∉ σ.spaces ⟨i.val - 1, by omega⟩ :=
  (exists_jhGapVector σ τ hσ hτ i hi).choose_spec.2

/-- The Jordan-Hölder gap vector lies in $V_i$. -/
theorem jhGapVector_mem_Vi (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    jhGapVector σ τ hσ hτ i hi ∈ σ.spaces i :=
  (Submodule.mem_inf.mp (jhGapVector_mem_inf σ τ hσ hτ i hi)).1

/-- The Jordan-Hölder gap vector lies in $W_{j+1}$, where $j$ is the jump column. -/
theorem jhGapVector_mem_Wj (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    jhGapVector σ τ hσ hτ i hi ∈
      τ.spaces ⟨(jumpCol σ τ hσ hτ i hi).val + 1, by omega⟩ :=
  (Submodule.mem_inf.mp (jhGapVector_mem_inf σ τ hσ hτ i hi)).2

/-- The Jordan-Hölder gap vector is nonzero. -/
theorem jhGapVector_ne_zero (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    jhGapVector σ τ hσ hτ i hi ≠ 0 := by
  intro heq
  exact jhGapVector_not_mem_lower σ τ hσ hτ i hi
    (heq ▸ (σ.spaces ⟨i.val - 1, by omega⟩).zero_mem)

end GLnBuilding
