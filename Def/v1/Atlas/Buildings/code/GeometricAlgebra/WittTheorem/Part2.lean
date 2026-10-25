/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/WittTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Lemma.Submodule.OfEq.eq.M.of.Eq
import Lemma.Fin.Nondegenerate.of.EqOrthogonalBilinFormTop_Bot.IsRefl
import Lemma.Submodule.Any_EqAndAll_Eq_V.of.IsSubspaceIsometry.EqOrthogonalBilinFormTop
import Theorem.v1.Atlas.Buildings.code.GeometricAlgebra.WittTheorem
set_option maxHeartbeats 4000000


namespace Garrett

variable {k : Type*} [Field k] [NeZero (2 : k)]

variable {V : Type*} [AddCommGroup V] [Module k V]


variable (B : LinearMap.BilinForm k V)

/-- The bilinear reflection through `a`, packaged as a linear equivalence
`V ≃ₗ[k] V` (using its involutive property). -/
noncomputable def bilinReflectEquiv (a : V) (ha : B a a ≠ 0) : V ≃ₗ[k] V :=
  LinearEquiv.ofInvolutive (bilinReflectLM B a ha) (bilinReflect_invol B a ha)

end Garrett
