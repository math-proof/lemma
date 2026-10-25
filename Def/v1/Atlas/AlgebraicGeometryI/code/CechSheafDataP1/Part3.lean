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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.CechSheafDataP1.Part2


noncomputable section

universe v

namespace CechSheafDataP1

open SerreDualityTate CanonicalSheafCurves GenusConstruction

open TateCechInfra

variable (k : Type) [Field k]


/-- The packaged `CechSheafData` instance for `P¹` with line bundle of degree `0`, the structure
sheaf, exhibiting Riemann–Roch for both `O` and `K`. -/
def cechSheafDataP1 : CechSheafData k where
  setup := tateSetupP1 k
  curve := P1 k
  deg := 0
  h0_E := 1
  h1_EK := 1
  hRR_E := by

    rw [finrank_cechH1_eq_zero]
    simp
    exact (P1_chi_O k).symm
  hRR_EK := by

    rw [finrank_dual_cechH0_eq_zero]
    simp
    rw [P1_degK]
    exact P1_chi_K k

end CechSheafDataP1
end
