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
import Instance.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective.Part3


noncomputable section

open KaehlerDifferential Module CanonicalSheafDef

universe u

section MvPolynomialSmooth

variable (k : Type u) [Field k] (n : ℕ)

/-- The cotangent (Kähler differentials) sheaf on `P^n`, presented as a graded module. -/
opaque cotangentSheafGM : GradedModuleData.{u, u} k n

/-- The canonical bundle of `P^n` (top exterior power of the cotangent sheaf), as a graded
module. By Prop 36 (Lec 20) this equals `O(-(n+1))`. -/
opaque canonicalBundleGM : GradedModuleData.{u, u} k n

/-- Specialisation to `P^1`: `K_{P^1} = O(-2)`. -/
def HasTwistDegree (M : GradedModuleData.{u, u} k n) (d : ℤ) : Prop :=
  ∀ i : ℤ, Nonempty (GrLinEquiv k n M (serreTwist k n d) i)

end MvPolynomialSmooth
end
