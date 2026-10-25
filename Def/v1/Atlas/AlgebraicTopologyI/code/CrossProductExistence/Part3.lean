/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CrossProductExistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.ModelChains
import Structure.v1.Atlas.AlgebraicTopologyI.code.CrossProductExistence.Part2
open Finset BigOperators


namespace AlgebraicTopologyI

noncomputable section

open ContinuousMap

/-- The fundamental singular `1`-simplex `ι₁ : Δ¹ → I` given on barycentric
coordinates `(t₀, t₁)` by `(t₀, t₁) ↦ t₁`. -/
noncomputable def iotaSimplex : SingularSimplex 1 ↥I where
  toFun t := ⟨t.1 1, by
    obtain ⟨hnn, hsum⟩ := t.2
    constructor
    · exact hnn 1
    · have h0 := hnn 0
      have : t.1 0 + t.1 1 = 1 := by
        have := hsum
        simp [Fin.sum_univ_two] at this
        exact this
      linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_apply 1).comp continuous_subtype_val

end
end AlgebraicTopologyI
