/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticLinearAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part2
open Module


namespace SymplecticLinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The kernel of `symplRestrict Ω E` is exactly the symplectic orthogonal $E^\Omega$. -/
lemma ker_symplRestrict (Ω : LinearMap.BilinForm ℝ V) (E : Submodule ℝ V) :
    LinearMap.ker (symplRestrict Ω E) = Ω.orthogonal E := by
  ext v
  simp only [LinearMap.mem_ker]
  constructor
  · intro hv u hu
    have := LinearMap.ext_iff.mp hv ⟨u, hu⟩
    simp [symplRestrict] at this
    exact this
  · intro hv
    ext ⟨u, hu⟩
    simp [symplRestrict]
    exact hv u hu


end SymplecticLinearAlgebra
