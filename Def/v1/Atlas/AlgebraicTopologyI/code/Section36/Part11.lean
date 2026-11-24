module
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section36.Part7
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace FullyRelativeCapProduct

variable (R : Type) [CommRing R]

/-- The induced map of relative singular chain complexes
`S_*(U \ L, (U \ L) ∩ Kᶜ; R) → S_*(Lᶜ, Lᶜ ∩ Kᶜ; R)` coming from the
inclusions of pairs. -/
def localityInclChainMap (X : TopCat.{0}) (K L : Set X)
    (pair : OpenNbhdPair K L) :
    relSingChainCx R (TopCat.of ↑(pair.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ⟶
    relSingChainCx R (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (localitySubIncl X K L pair))
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (localityBigIncl X L pair))
    (localityIncl_comm_chain R X K L pair)

/-- The induced map on relative homology
`H_q(U \ L, (U \ L) ∩ Kᶜ; R) → H_q(Lᶜ, Lᶜ ∩ Kᶜ; R)`, which is the second
ingredient (after excision) of the local construction of the fully relative
cap product. -/
def localityForwardHomol
    (X : TopCat.{0}) (K L : Set X)
    (pair : OpenNbhdPair K L) (q : ℕ) :
    (relSingularHomology R (TopCat.of ↑(pair.U.1 \ L))
      (Subtype.val ⁻¹' Kᶜ) q : Type _) →ₗ[R]
      (relSingularHomology R (TopCat.of (Lᶜ : Set X))
        (complementInComplement X K L) q : Type _) :=
  (HomologicalComplex.homologyMap (localityInclChainMap R X K L pair) q).hom


/-- The fully relative cap product at a single open neighbourhood pair: given
a cohomology class in `H^p(U, V; R)`, it produces an `R`-linear map
`H_n(X, Kᶜ; R) → H_q(Lᶜ, Lᶜ ∩ Kᶜ; R)` by composing inverse excision,
`relCapProductOnNbhd`, and `localityForwardHomol`. -/
def nbhdSubIncl_n
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑pair₂.U.1)) ⟶
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑pair₁.U.1)) :=
  ⟨fun ⟨⟨x, hxU₂⟩, hxK⟩ => ⟨⟨x, h.1 hxU₂⟩, hxK⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

end FullyRelativeCapProduct
end
