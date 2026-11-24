module
public import Def.v1.Atlas.AlgebraicGeometryI.code.TwistSheaf.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.TwistSheaf
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleProjective
public import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective.Part4
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec20EulerSequence
set_option maxHeartbeats 800000
open QCohProjective TwistSheaf


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20EulerSequence.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace EulerSequence

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-- The type of graded module data on `ℙⁿ` is inhabited (witnessed by the structure sheaf). -/
instance : Nonempty (GradedModuleData.{u, u} k n) :=
  ⟨structureSheafData k n⟩

end EulerSequence
end
