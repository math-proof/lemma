/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityLinear.Part4
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityLinear
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ResidueSum
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityGeneral
import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityCurves.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueSum
import Instance.v1.Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityTate.Part2


noncomputable section

namespace SerreDualityTate

open CanonicalSheafCurves RiemannRochCurves SerreDualityP1

open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology

open SerreDualityCurves


section AnnihilatorIdentities

variable {k : Type*} [Field k]

/-- Tate vector space (Def 46, Lec 25): a `k`-vector space `V` with a topology
admitting a neighborhood basis of `0` by mutually commensurable subspaces. -/
structure TateVectorSpace where
  V : Type*
  [instACG : AddCommGroup V]
  [instModule : Module k V]
  topology : TopologicalSpace V
  nhd_basis : Set (Submodule k V)
  is_nhd_basis : ∀ U ∈ nhd_basis, (U : Set V) ∈ @nhds V topology 0
  commensurable : ∀ U₁ ∈ nhd_basis, ∀ U₂ ∈ nhd_basis,
    Module.Finite k (U₁ ⧸ Submodule.comap U₁.subtype (U₁ ⊓ U₂)) ∧
    Module.Finite k (U₂ ⧸ Submodule.comap U₂.subtype (U₁ ⊓ U₂))

end AnnihilatorIdentities
end SerreDualityTate
end
