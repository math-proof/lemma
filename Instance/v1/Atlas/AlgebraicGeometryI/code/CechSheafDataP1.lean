/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.CechCohomologyIdentification
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CechCohomologyIdentification
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GenusConstruction
import Def.v1.Atlas.AlgebraicGeometryI.code.GenusConstruction.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.CechSheafDataP1


noncomputable section

universe v

namespace CechSheafDataP1

open SerreDualityTate CanonicalSheafCurves GenusConstruction

open TateCechInfra

variable (k : Type) [Field k]


instance : FiniteDimensional k (tateSetupP1 k).V :=
  inferInstanceAs (FiniteDimensional k k)


end CechSheafDataP1
end
