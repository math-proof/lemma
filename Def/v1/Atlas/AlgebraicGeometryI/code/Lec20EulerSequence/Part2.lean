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
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec20EulerSequence
set_option maxHeartbeats 800000

open QCohProjective TwistSheaf


noncomputable section

namespace EulerSequence

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-- The cotangent sheaf `Ω_{ℙⁿ/k}` as a graded module datum; sits as the left term in the
Euler sequence `0 → Ω_{ℙⁿ} → O(-1)^{n+1} → O → 0`. -/
noncomputable def canonicalBundleGM : GradedModuleData.{u, u} k n :=
  serreTwist k n (-(↑n + 1 : ℤ))

end EulerSequence
end
