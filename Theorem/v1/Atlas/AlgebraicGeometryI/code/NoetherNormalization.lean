/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NoetherNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.DimensionProduct
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DimensionProduct
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.NakayamaApplications
import Theorem.v1.Atlas.AlgebraicGeometryI.code.NakayamaApplications
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec2AlgebraicVariety
set_option maxHeartbeats 800000


noncomputable section

open MvPolynomial PrimeSpectrum

section NoetherNormalization

variable (k : Type*) [Field k] (A : Type*) [CommRing A] [Nontrivial A]
  [Algebra k A] [Algebra.FiniteType k A]

end NoetherNormalization
end
