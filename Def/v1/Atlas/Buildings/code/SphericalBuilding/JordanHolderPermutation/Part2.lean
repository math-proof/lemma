/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.RefinementDimJumps
import Lemma.Fin.FinrankKSpacesValAdd1.of.IsStrictFlag
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.JordanHolderPermutation.Part2
set_option maxHeartbeats 800000


namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- Choice of the **Jordan-Hölder gap vector** at row $i$: an explicit witness in
$V_i \cap W_{j+1} \setminus V_{i-1}$ where $j$ is the jump column. -/
noncomputable def jhGapVector (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) : Vec k n :=
  (exists_jhGapVector σ τ hσ hτ i hi).choose

end GLnBuilding
