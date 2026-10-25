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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section36.Part9
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


noncomputable section

namespace FullyRelativeCapProduct

variable (R : Type) [CommRing R]

/-- The chain map between relative chain complexes
`S_*(U₂ \ L, (U₂ \ L) ∩ Kᶜ) → S_*(U₁ \ L, (U₁ \ L) ∩ Kᶜ)` induced by passing
to a smaller pair (on the `q`-side). -/
def nbhdInclChainMap_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    relSingChainCx R (TopCat.of ↑(pair₂.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ⟶
    relSingChainCx R (TopCat.of ↑(pair₁.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (nbhdSubIncl_q pair₁ pair₂ h))
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (nbhdBigIncl_q pair₁ pair₂ h))
    (nbhdIncl_comm_chain_q R pair₁ pair₂ h)


/-- The map on relative homology
`H_q(U₂ \ L, (U₂ \ L) ∩ Kᶜ; R) → H_q(U₁ \ L, (U₁ \ L) ∩ Kᶜ; R)` induced by
passing to a smaller pair (on the `q`-side). -/
def nbhdHomologyInclusion_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) (q : ℕ) :
    (relSingularHomology R (TopCat.of ↑(pair₂.U.1 \ L))
      (Subtype.val ⁻¹' Kᶜ) q : Type _) →ₗ[R]
      (relSingularHomology R (TopCat.of ↑(pair₁.U.1 \ L))
        (Subtype.val ⁻¹' Kᶜ) q : Type _) :=
  (HomologicalComplex.homologyMap (nbhdInclChainMap_q R pair₁ pair₂ h) q).hom

/-- Compatibility of inverse excision with the transition maps between
nested neighbourhood pairs: lifting `y ∈ H_n(X, Kᶜ; R)` to a class in
`pair₁.U` agrees with first lifting to `pair₂.U` and then transporting to
`pair₁.U` via `nbhdHomologyInclusion_n`. -/
def absNbhdHomologyIncl
    {X : TopCat.{0}} {K : Set X}
    (U₁ U₂ : CechCohomology.OpenNeighborhoods K) (_h : U₁ ≤ U₂) (n : ℕ) :
    (relSingularHomology R (TopCat.of ↑U₂.1.1)
      (Subtype.val ⁻¹' Kᶜ) n : Type _) →ₗ[R]
      (relSingularHomology R (TopCat.of ↑U₁.1.1)
        (Subtype.val ⁻¹' Kᶜ) n : Type _) := by
  classical
  exact (excisionInverseHomol R X K U₁.1 U₁.2 n).comp
    ((excisionForwardHomol R X K U₂.1 n).hom)


/-- The composite naturality statement assembling
`absExcisionForward_compatible`, `absCapOnNbhd_naturality` and
`absNbhdExcisionInverse_compatible` for the absolute cap product. -/
def absToRelHomol
    (X : TopCat.{0}) (K : Set X) (n : ℕ) :
    absSingularHomology R X n ⟶ relSingularHomology R X Kᶜ n :=
  HomologicalComplex.homologyMap (cokernel.π (inclChainMap R X Kᶜ)) n


/-- A chain-level splitting/section of relative chains
`S_*(Lᶜ, Lᶜ ∩ Kᶜ; R) → S_*(Lᶜ; R)`, used to construct the comparison map
between the relative and absolute homology groups appearing in Theorem 36.1. -/

end FullyRelativeCapProduct

open Set FullyRelativeCapProduct

/-- The standing hypothesis for the Čech/singular Mayer–Vietoris compatibility
theorem: either `X` is a normal space and `A, B` are closed in `X`, or `X` is
Hausdorff and `A, B` are compact. -/
def MayerVietorisHypothesis (X : Type*) [TopologicalSpace X]
    (A B : Set X) : Prop :=
  (NormalSpace X ∧ IsClosed A ∧ IsClosed B) ∨
  (T2Space X ∧ IsCompact A ∧ IsCompact B)

end
