/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoffGeometric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.GBSplittingExistence.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GBSplittingExistence
import Def.v1.Atlas.AlgebraicGeometryI.code.GrothendieckBirkhoffGeometric
open BigOperators


namespace GBGeometric

/-- `k[x]` is a principal ideal domain (used to access the structure theorem on `P^1`). -/
instance polynomial_pid (k : Type*) [Field k] :
    IsPrincipalIdealRing (Polynomial k) :=
  inferInstance

end GBGeometric
