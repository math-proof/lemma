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
import Def.v1.Atlas.AlgebraicGeometryI.code.CechSheafDataP1.Part2


noncomputable section

universe v

namespace CechSheafDataP1

open SerreDualityTate CanonicalSheafCurves GenusConstruction

open TateCechInfra

variable (k : Type) [Field k]


/-- The degree of the canonical bundle of `P¹` is `-2`. -/
lemma P1_degK : (P1 k).degK = -2 := P1CurveFromCech_degK k

/-- The Euler characteristic of the structure sheaf of `P¹` is `1`. -/
lemma P1_chi_O : (P1 k).χ (1, 0) = 1 := by
  exact (P1 k).hχ_struct

/-- The Euler characteristic of the canonical bundle of `P¹` is `-1`. -/
lemma P1_chi_K : (P1 k).χ (1, -2) = -1 := by
  exact (P1 k).hχ_canonical


end CechSheafDataP1
end
