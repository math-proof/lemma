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
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.JordanHolderFrame
set_option maxHeartbeats 800000


namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- The **Jordan-Hölder frame** of two complete flags $\sigma, \tau$: the apartment frame
whose lines are spanned by the Jordan-Hölder gap vectors $\ell_i$, simultaneously refining both
flags. -/
noncomputable def jordanHolderFrame (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) [FiniteDimensional k (Vec k n)] :
    Frame k n where
  lines i := k ∙ (jhLine σ τ hσ hτ i)
  one_dim i := finrank_span_singleton (jhLine_ne_zero σ τ hσ hτ i)
  indep := (jhLine_linearIndependent σ τ hσ hτ).iSupIndep_span_singleton
  spanning := by
    rw [← Submodule.span_range_eq_iSup]
    exact jhLine_span_eq_top σ τ hσ hτ

end GLnBuilding
