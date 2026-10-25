/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Algebra.Group.Subgroup.Ker
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section36.Part8
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


noncomputable section

namespace FullyRelativeCapProduct

variable (R : Type) [CommRing R]

/-- The chain map between relative chain complexes
`S_*(U₂, U₂ ∩ Kᶜ) → S_*(U₁, U₁ ∩ Kᶜ)` induced by passing to a smaller pair
(on the `n`-side). -/
def nbhdInclChainMap_n
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    relSingChainCx R (TopCat.of ↑pair₂.U.1) (Subtype.val ⁻¹' Kᶜ) ⟶
    relSingChainCx R (TopCat.of ↑pair₁.U.1) (Subtype.val ⁻¹' Kᶜ) :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (nbhdSubIncl_n pair₁ pair₂ h))
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (opensInclusion pair₁.U pair₂.U h.1))
    (nbhdIncl_comm_chain_n R pair₁ pair₂ h)


/-- The map on relative homology
`H_n(U₂, U₂ ∩ Kᶜ; R) → H_n(U₁, U₁ ∩ Kᶜ; R)` induced by passing to a smaller
pair (on the `n`-side). -/
def nbhdHomologyInclusion_n
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) (n : ℕ) :
    (relSingularHomology R (TopCat.of ↑pair₂.U.1)
      (Subtype.val ⁻¹' Kᶜ) n : Type _) →ₗ[R]
      (relSingularHomology R (TopCat.of ↑pair₁.U.1)
        (Subtype.val ⁻¹' Kᶜ) n : Type _) :=
  (HomologicalComplex.homologyMap (nbhdInclChainMap_n R pair₁ pair₂ h) n).hom

/-- The inclusion `U₂ \ L ↪ U₁ \ L` for two nested neighbourhood pairs,
as a morphism in `TopCat`. -/
def nbhdBigIncl_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    TopCat.of ↑(pair₂.U.1 \ L) ⟶ TopCat.of ↑(pair₁.U.1 \ L) :=
  ⟨fun ⟨x, hx⟩ => ⟨x, h.1 hx.1, hx.2⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val⟩

/-- The inclusion `(U₂ \ L) ∩ Kᶜ ↪ (U₁ \ L) ∩ Kᶜ` for two nested neighbourhood
pairs, as a morphism in `TopCat` (on the `q`-side). -/
def nbhdSubIncl_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑(pair₂.U.1 \ L))) ⟶
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑(pair₁.U.1 \ L))) :=
  ⟨fun ⟨⟨x, hx⟩, hxK⟩ => ⟨⟨x, h.1 hx.1, hx.2⟩, hxK⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

end FullyRelativeCapProduct
end
