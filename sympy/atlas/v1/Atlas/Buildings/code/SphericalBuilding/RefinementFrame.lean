/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementFrame.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.SphericalBuilding.RefinementDimJumps
import Lemma.Fin.FinrankKSpacesValAdd1.of.IsStrictFlag
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- Choice of a **gap vector** at step $i$ of a strict flag: a vector in $V_{i+1} \setminus V_i$. -/
noncomputable def CompleteFlag.IsStrictFlag.gapVector {σ : CompleteFlag k n}
    (hσ : σ.IsStrictFlag) (i : Fin n) : Vec k n :=
  (SetLike.exists_of_lt (hσ.spaces_lt i)).choose

/-- The **refinement frame** of a strict flag: the apartment frame whose lines are spanned by
the gap vectors $v_i$, giving an apartment containing $\sigma$ as a chamber. -/
noncomputable def refinementFrame {σ : CompleteFlag k n}
    (hσ : σ.IsStrictFlag) [FiniteDimensional k (Vec k n)] : Frame k n where
  lines i := k ∙ (hσ.gapVector i)
  one_dim i := finrank_span_singleton (hσ.gapVector_ne_zero i)
  indep := hσ.linearIndependent_gapVectors.iSupIndep_span_singleton
  spanning := by
    rw [← Submodule.span_range_eq_iSup]
    exact hσ.span_gapVectors_eq_top

/-- Wrapper: the refinement frame of a strict flag $\sigma$, ignoring a second flag $\tau$. -/
noncomputable def refinementFrameFromPair (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (_hτ : τ.IsStrictFlag) [FiniteDimensional k (Vec k n)] :
    Frame k n :=
  refinementFrame hσ

end GLnBuilding
