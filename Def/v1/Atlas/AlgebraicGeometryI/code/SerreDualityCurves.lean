/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityLinear
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ResidueSum
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DedekindCurve
import Instance.v1.Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityLinear.Part4
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityGeneral
import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueSum
import Def.v1.Atlas.AlgebraicGeometryI.code.DedekindCurve


noncomputable section

namespace SerreDualityCurves

open CanonicalSheafCurves RiemannRochCurves SerreDualityP1

open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology


section ResidueMap

variable (k : Type*) [Field k]

/-- The residue map `(ℤ →₀ k) →ₗ[k] k` sending a Laurent polynomial to its
coefficient at index `-1`. -/
def residueMap : (ℤ →₀ k) →ₗ[k] k where
  toFun f := f (-1)
  map_add' f g := Finsupp.add_apply f g (-1)
  map_smul' c f := Finsupp.smul_apply c f (-1)

/-- Coefficient of the formal derivative: `(d/dz f)(m) = (m+1) · f(m+1)`. -/
def derivCoeff (f : ℤ →₀ k) (m : ℤ) : k :=
  (↑(m + 1) : k) * f (m + 1)

/-- The residue pairing `⟨f, g⟩ = ∑ i f(i) · g(-1 - i)`, which extracts
the `-1`-coefficient of the convolution product. -/
def residuePairing (f g : ℤ →₀ k) : k :=
  ∑ i ∈ f.support, f i * g (-1 - i)

end ResidueMap
end SerreDualityCurves
end
