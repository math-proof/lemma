/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20EulerSequence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.TwistSheaf.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.TwistSheaf
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleProjective
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective.Part4
import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec20EulerSequence
set_option maxHeartbeats 800000

open QCohProjective TwistSheaf


noncomputable section

namespace EulerSequence

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-- The graded module `O(-1)^{n+1}` on `ℙⁿ`, formed as a `(n+1)`-fold direct sum of the
Serre twist `O(-1)`; this is the middle term of the Euler sequence. -/
def directSumTwist : GradedModuleData.{u, u} k n where
  component d := Fin (n + 1) → (serreTwist k n (-1)).component d
  instACG _d := Pi.addCommGroup
  instMod d := @Pi.module (Fin (n + 1)) (fun _ => (serreTwist k n (-1)).component d) k _
    (fun _ => ((serreTwist k n (-1)).instACG d).toAddCommMonoid)
    (fun _ => (serreTwist k n (-1)).instMod d)
  gsmul i j s v := fun idx =>
    (serreTwist k n (-1)).gsmul i j s (v idx)

end EulerSequence
end
