/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
import Theorem.v1.Atlas.GeometryOfManifolds.code.Counterexamples.Part2
set_option autoImplicit false

open DifferentialFormSpace


namespace KTGamma

/-- The "third generator" $(0,0,1,0) \in \Gamma$, which lies in the commutator subgroup. -/
def generator3 : KTGamma := mk 0 0 1 0

end KTGamma
