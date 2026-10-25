/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderFrame.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.JordanHolderPermutation.Part3
import Lemma.Fin.LeFinrank.of.Le.GtVal_0
import Lemma.Fin.GapVector.in.Spaces.of.LtVal_Val.IsStrictFlag
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.RefinementCompatibility
set_option maxHeartbeats 800000


namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- The $i$-th **Jordan-Hölder line vector** for two complete strict flags $\sigma, \tau$: a
nonzero vector representing the gap $V_{i+1}/V_i$ in the Schreier refinement of $\sigma$ by $\tau$. -/
noncomputable def jhLine (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) (i : Fin n) : Vec k n :=
  jhGapVector σ τ hσ hτ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)

end GLnBuilding
