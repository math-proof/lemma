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
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section36.Part2
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


noncomputable section

open Set FullyRelativeCapProduct

/-- The Mayer–Vietoris union-to-sum map in Čech cohomology,
`Ȟ^p(A ∪ B; R) → Ȟ^p(A; R) ⊕ Ȟ^p(B; R)`, given by pairing the two
restriction maps. -/
def singularMV_unionToSum
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (_hyp : MayerVietorisHypothesis X A B) (q : ℕ) :
    (relSingularHomology R X (A ∪ B)ᶜ q ⟶
      relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q) :=
  biprod.lift
    (homolRestriction R X (A ∪ B) A q)
    (homolRestriction R X (A ∪ B) B q)


/-- The Mayer–Vietoris sum-to-intersection map in relative singular homology
of the complements, `H_q(X, Aᶜ) ⊕ H_q(X, Bᶜ) → H_q(X, (A ∩ B)ᶜ)`, given by
the difference of the restriction maps. -/
def singularMV_sumToInter
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (_hyp : MayerVietorisHypothesis X A B) (q : ℕ) :
    (relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q ⟶
      relSingularHomology R X (A ∩ B)ᶜ q) :=
  biprod.desc
    (homolRestriction R X A (A ∩ B) q)
    (-(homolRestriction R X B (A ∩ B) q))


/-- The Mayer–Vietoris connecting morphism in relative singular homology of
the complements, `H_q(X, (A ∩ B)ᶜ) → H_{q-1}(X, (A ∪ B)ᶜ)`, witnessing the
long exact sequence under the Mayer–Vietoris hypothesis. -/
def inclusionForwardHomol
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (U : CechCohomology.OpenNeighborhoods S) (q : ℕ) :
    (relSingularHomology R (TopCat.of ↑U.1.1)
      (Subtype.val ⁻¹' Sᶜ) q : Type _) →ₗ[R]
      (relSingularHomology R X Sᶜ q : Type _) :=
  (excisionForwardHomol R X S U.1 q).hom


/-- The transition map on relative singular homology between two
neighbourhoods `U₁ ≤ U₂` of `S`, obtained as the composition of the
inclusion-induced map `U₂ → X` with the inverse of the excision isomorphism
for `U₁`. -/
def absNbhdHomologyInclusion
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (U₁ U₂ : CechCohomology.OpenNeighborhoods S) (_h : U₁ ≤ U₂) (n : ℕ) :
    (relSingularHomology R (TopCat.of ↑U₂.1.1)
      (Subtype.val ⁻¹' Sᶜ) n : Type _) →ₗ[R]
      (relSingularHomology R (TopCat.of ↑U₁.1.1)
        (Subtype.val ⁻¹' Sᶜ) n : Type _) := by
  classical
  exact (excisionInverseHomol R X S U₁.1 U₁.2 n).comp
    ((excisionForwardHomol R X S U₂.1 n).hom)

end
