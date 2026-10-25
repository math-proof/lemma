/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafDef
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.TwistSheaf
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafDef.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.TwistSheaf.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective.Part3


noncomputable section

open KaehlerDifferential Module CanonicalSheafDef

universe u

section MvPolynomialSmooth

variable (k : Type u) [Field k] (n : ℕ)

/-- The structure sheaf provides a default graded module on `P^n`, giving inhabitedness. -/
instance : Nonempty (GradedModuleData.{u, u} k n) :=
  ⟨structureSheafData k n⟩

end MvPolynomialSmooth
end
