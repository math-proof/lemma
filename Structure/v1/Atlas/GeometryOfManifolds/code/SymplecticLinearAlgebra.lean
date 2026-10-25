/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticLinearAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Module


namespace SymplecticLinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A bilinear form $\Omega$ on a real vector space $V$ is symplectic iff it is alternating
($\Omega(v,v) = 0$) and nondegenerate (its left radical is trivial). -/
structure IsSymplecticForm (Ω : LinearMap.BilinForm ℝ V) : Prop where
  alt : Ω.IsAlt
  nondeg : Ω.SeparatingLeft

end SymplecticLinearAlgebra
