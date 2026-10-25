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
import Structure.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective


noncomputable section

open KaehlerDifferential Module CanonicalSheafDef

universe u

section MvPolynomialSmooth

variable (k : Type u) [Field k] (n : ℕ)

/-- Middle term of the Euler sequence on `P^n`: the direct sum `O(-1)^{n+1}`. -/
def directSumTwist : GradedModuleData.{u, u} k n where
  component d := Fin (n + 1) → (serreTwist k n (-1)).component d
  instACG _d := Pi.addCommGroup
  instMod d := @Pi.module (Fin (n + 1)) (fun _ => (serreTwist k n (-1)).component d) k _
    (fun _ => ((serreTwist k n (-1)).instACG d).toAddCommMonoid)
    (fun _ => (serreTwist k n (-1)).instMod d)
  gsmul i j s v := fun idx =>
    (serreTwist k n (-1)).gsmul i j s (v idx)

end MvPolynomialSmooth
end
