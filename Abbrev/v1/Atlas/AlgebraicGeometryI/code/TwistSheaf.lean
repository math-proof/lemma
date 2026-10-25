/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.QCohProjective.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.QCohProjective
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.QCohEquivalenceProof
import Instance.v1.Atlas.AlgebraicGeometryI.code.QCohEquivalenceProof
import Def.v1.Atlas.AlgebraicGeometryI.code.TwistSheaf
set_option maxHeartbeats 4000000

open MvPolynomial QCohProjective


noncomputable section

namespace TwistSheaf

variable (k : Type*) [Field k] (n : ℕ)


/-- The degree-`d` graded component as a type. -/
abbrev polyGrComp (d : ℤ) : Type _ := ↥(polyGrSub k n d)

end TwistSheaf
end
