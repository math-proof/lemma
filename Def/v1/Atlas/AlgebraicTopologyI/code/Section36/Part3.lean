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
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section36.Part2
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


noncomputable section

namespace FullyRelativeCapProduct

variable (R : Type) [CommRing R]

/-- The transition map `relCohomOfPair pair₁ p → relCohomOfPair pair₂ p` in the
directed system of open neighbourhood pairs, induced by restriction of cochains
along the inclusions `pair₂.U ⊆ pair₁.U` and `pair₂.V ⊆ pair₁.V`. -/
def relCechTransition {X : TopCat.{0}} {K L : Set X}
    (p : ℕ) (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    relCechFamily R p pair₁ →ₗ[R] relCechFamily R p pair₂ := by
  classical

  let G := ModuleCat.of R R
  let F := (singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj G
  let L' := ((linearYoneda R (ModuleCat.{0} R)).obj G).rightOp.mapHomologicalComplex
    (ComplexShape.down ℕ)
  let U := HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)


  let restrictMap₁ := U.map ((L'.map (F.map (opensInclusion pair₁.U pair₁.V pair₁.hVU))).op)
  let restrictMap₂ := U.map ((L'.map (F.map (opensInclusion pair₂.U pair₂.V pair₂.hVU))).op)

  let pU := U.map ((L'.map (F.map (opensInclusion pair₁.U pair₂.U h.1))).op)
  let qV := U.map ((L'.map (F.map (opensInclusion pair₁.V pair₂.V h.2))).op)

  have comm : restrictMap₁ ≫ qV = pU ≫ restrictMap₂ := by
    simp only [restrictMap₁, restrictMap₂, pU, qV]
    simp only [← U.map_comp, ← op_comp, ← L'.map_comp, ← F.map_comp]


    have : opensInclusion pair₁.V pair₂.V h.2 ≫ opensInclusion pair₁.U pair₁.V pair₁.hVU =
        opensInclusion pair₂.U pair₂.V pair₂.hVU ≫ opensInclusion pair₁.U pair₂.U h.1 := by
      ext ⟨x, hx⟩; rfl
    rw [this]

  exact (HomologicalComplex.homologyMap
    (kernel.map restrictMap₁ restrictMap₂ pU qV comm) p).hom


/-- The relative Čech cohomology `Ȟ^p(K, L; R)`, defined as the direct limit
of the relative singular cohomologies `H^p(U, V; R)` over the cofinal system
of `OpenNbhdPair`s shrinking down to `(K, L)`. -/
def cechCohomologyRel
    (X : TopCat.{0}) (K L : Set X) (p : ℕ) : ModuleCat.{0} R := by
  classical
  exact ModuleCat.of R (Module.DirectLimit
    (relCechFamily (R := R) (X := X) (K := K) (L := L) p)
    (fun pair₁ pair₂ h => relCechTransition R p pair₁ pair₂ h))

/-- The subset `(X - K) ∩ (X - L) ⊆ X - L`, encoded as the preimage of `Kᶜ`
inside the subspace `Lᶜ`. -/
def complementInComplement (X : TopCat.{0}) (K L : Set X) :
    Set (TopCat.of (Lᶜ : Set X)) :=
  Subtype.val ⁻¹' (Kᶜ : Set X)

/-- Extract the open neighbourhood of `K` from an `OpenNbhdPair K L`. -/
def pairToNbhdK {X : Type} [TopologicalSpace X] {K L : Set X}
    (pair : OpenNbhdPair K L) : CechCohomology.OpenNeighborhoods K :=
  ⟨pair.U, pair.hK⟩

/-- Extract the open neighbourhood of `L` from an `OpenNbhdPair K L`. -/
def pairToNbhdL {X : Type} [TopologicalSpace X] {K L : Set X}
    (pair : OpenNbhdPair K L) : CechCohomology.OpenNeighborhoods L :=
  ⟨pair.V, pair.hL⟩


/-- For a single neighbourhood pair, the map from the relative cohomology
`H^p(U, V; R)` to absolute Čech cohomology `Ȟ^p(K; R)`, obtained by forgetting
the relativity (via the kernel inclusion) and then injecting into the
direct limit. -/
def nbhdRestrictToLimit {X : TopCat.{0}} {K L : Set X}
    (p : ℕ) (pair : OpenNbhdPair K L) :
    relCechFamily R p pair →ₗ[R]
      (CechCohomology.cechCohomology R K p : Type _) := by
  classical
  let G := ModuleCat.of R R

  let rMap := SingularCohomology.restrictionCochainMap R G
    (opensInclusion pair.U pair.V pair.hVU)


  let forgetful : relCechFamily R p pair →ₗ[R]
      CechCohomology.cechFamily R K p (pairToNbhdK pair) :=
    (HomologicalComplex.homologyMap (kernel.ι rMap) p).hom

  let intoLimit := Module.DirectLimit.of R _
    (CechCohomology.cechFamily R K p)
    (fun U V h => CechCohomology.cechTransition R K p U V h)
    (pairToNbhdK pair)
  exact intoLimit.comp forgetful


/-- Compatibility of `nbhdRestrictToLimit` with the transition maps of the
neighbourhood-pair directed system; required for assembling the maps into a
well-defined map on the direct limit. -/
def nbhdToSubspaceViaLimit {X : TopCat.{0}} {K : Set X} (L : Set X)
    (p : ℕ) (U : CechCohomology.OpenNeighborhoods K) :
    CechCohomology.cechFamily R K p U →ₗ[R]
      (CechCohomology.cechCohomology R L p : Type _) := by
  classical
  by_cases hLK : L ⊆ K
  · have hLU : L ⊆ ↑U.1 := fun x hx => U.2 (hLK hx)
    exact Module.DirectLimit.of R _
      (CechCohomology.cechFamily R L p)
      (fun V₁ V₂ h => CechCohomology.cechTransition R L p V₁ V₂ h)
      ⟨U.1, hLU⟩
  · exact 0


/-- Compatibility of `nbhdToSubspaceViaLimit` with the Čech transition maps,
required to define a map on the direct limit `Ȟ^p(K; R) → Ȟ^p(L; R)`. -/
def subsetInclusion (X : TopCat.{0}) (A B : Set X) (h : A ⊆ B) :
    TopCat.of A ⟶ TopCat.of B :=
  ⟨Set.inclusion h, continuous_inclusion h⟩

end FullyRelativeCapProduct
end
