/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.SerreDualityTate
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityTate
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityAnnihilator
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.SerreDualityAnnihilator


section TateVectorSpaceDef

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Two subspaces `W₁`, `W₂` of `V` are commensurable iff their quotients by
their intersection are both finite-dimensional. -/
def IsCommensurable (W₁ W₂ : Submodule k V) : Prop :=
  Module.Finite k (W₁ ⧸ Submodule.comap W₁.subtype (W₁ ⊓ W₂)) ∧
  Module.Finite k (W₂ ⧸ Submodule.comap W₂.subtype (W₁ ⊓ W₂))

/-- A Tate vector space over `k` (Def 46, Lec 25): a topological `k`-vector
space whose neighborhood basis of zero consists of pairwise commensurable
linear subspaces. -/
class IsTateVectorSpace (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
    [TopologicalSpace V] : Prop where
  exists_nhds_basis : ∃ (ι : Type*) (W : ι → Submodule k V),
    (nhds (0 : V)).HasBasis (fun _ : ι => True) (fun i => ↑(W i)) ∧
    ∀ i j, IsCommensurable (W i) (W j)

end TateVectorSpaceDef

noncomputable section

universe v

namespace TateCechInfra

open SerreDualityTate SerreDualityCurves
open CanonicalSheafCurves RiemannRochCurves SerreDualityP1
open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology
open SerreDualityAnnihilator

variable (k : Type*) [Field k]

/-- Packaging the data needed to apply Tate self-duality machinery to a Čech
cohomology setup on a smooth complete curve, recording the Riemann–Roch
identities for both `E` and the dualized line bundle `K - E`. -/
structure CechSheafData where
  setup : TateDualitySetup.{_, v} k
  [instFD : FiniteDimensional k setup.V]
  curve : SmoothCompleteCurve
  deg : ℤ
  h0_E : ℤ
  h1_EK : ℤ
  hRR_E : h0_E - ↑(Module.finrank k setup.cechH1) = curve.χ (1, deg)
  hRR_EK : ↑(Module.finrank k ↥setup.dual.cechH0) - h1_EK =
            curve.χ (1, curve.degK - deg)

attribute [instance] CechSheafData.instFD

variable {k}

/-- The dimension of `H¹(E)` as an integer, extracted from the Čech data. -/
def CechSheafData.h1_E (D : CechSheafData k) : ℤ :=
  ↑(Module.finrank k D.setup.cechH1)

/-- The dimension of `H⁰(K - E)` as an integer, extracted from the Čech data. -/
def CechSheafData.h0_EK (D : CechSheafData k) : ℤ :=
  ↑(Module.finrank k ↥D.setup.dual.cechH0)
