/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section31.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section32
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Lemma32_4
import Def.v1.Atlas.AlgebraicTopologyI.code.Section32.Part2
import Def.v1.Atlas.AlgebraicTopologyI.code.Lemma32_4
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.LocallyConstant.Basic
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section31
open Topology MulAction CategoryTheory TopologicalSpace

open CategoryTheory AlgebraicTopology SingularCohomology Limits


noncomputable section

namespace OrientationHomology

/-- The inclusion of a subspace `A ⊆ M` as a morphism in `TopCat`. -/
def subsetIncl (M : Type) [TopologicalSpace M] (A : Set M) :
    TopCat.of A ⟶ TopCat.of M :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The relative singular chain complex `S_*(M, A; R)`, defined as the cokernel of the
chain map induced by the inclusion `A ↪ M`. -/
def relativeChainComplex (R : Type) [CommRing R]
    (M : Type) [TopologicalSpace M] (A : Set M) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  cokernel ((singularChainFunctor R).map (subsetIncl M A))

/-- The relative singular homology module `H_n(M, A; R)` of the pair `(M, A)`. -/
def relativeHomologyModule (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] (A : Set M) :
    ModuleCat.{0} R :=
  (relativeChainComplex R M A).homology n

/-- The local homology module `H_n(M, M − {x}; R)` at the point `x`; the stalk of the
orientation sheaf in degree `n`. -/
def localHomologyModule (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] (x : M) :
    ModuleCat.{0} R :=
  relativeHomologyModule R n M ({x}ᶜ)

/-- The inclusion `A ↪ B` as a morphism in `TopCat`, given `A ⊆ B`. -/
def subsetToSubset (M : Type) [TopologicalSpace M]
    (A B : Set M) (h : A ⊆ B) :
    TopCat.of A ⟶ TopCat.of B :=
  ⟨fun a => ⟨a.1, h a.2⟩, continuous_inclusion h⟩

/-- For `A ⊆ B`, the natural chain map between the relative chain complexes
`S_*(M, A; R) → S_*(M, B; R)` induced by the inclusion of subcomplexes. -/
def restrictionChainMap (R : Type) [CommRing R]
    (M : Type) [TopologicalSpace M] (A B : Set M) (h : A ⊆ B) :
    relativeChainComplex R M A ⟶ relativeChainComplex R M B := by
  apply cokernel.map _ _
    ((singularChainFunctor R).map (subsetToSubset M A B h)) (𝟙 _)
  simp only [Category.comp_id]
  show (singularChainFunctor R).map (subsetIncl M A) =
    (singularChainFunctor R).map (subsetToSubset M A B h) ≫
    (singularChainFunctor R).map (subsetIncl M B)
  rw [← Functor.map_comp]; congr 1

/-- The induced map on relative homology `H_n(M, A; R) → H_n(M, B; R)` for `A ⊆ B`. -/
def restrictionHomologyMap (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M]
    (A B : Set M) (h : A ⊆ B) :
    relativeHomologyModule R n M A ⟶ relativeHomologyModule R n M B :=
  HomologicalComplex.homologyMap (restrictionChainMap R M A B h) n

/-- The restriction map `H_n(M, M − U; R) → H_n(M, M − {y}; R) = (o_M)_y` from a
"compatible class over `U`" to its local-homology value at any point `y ∈ U`. -/
def restrictToPoint (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M]
    (U : Set M) (y : M) (hy : y ∈ U) :
    relativeHomologyModule R n M Uᶜ ⟶ localHomologyModule R n M y :=
  restrictionHomologyMap R n M Uᶜ {y}ᶜ
    (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy))

/-- A choice of local-homology element at each point is *locally compatible* if every
point has an open neighborhood `U` and a relative-homology class on `(M, M − U)` that
restricts to the chosen element at every point of `U`. -/
def IsLocallyCompatibleSection (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M]
    (μ : (x : M) → ↥(localHomologyModule R n M x)) : Prop :=
  ∀ x : M, ∃ (U : Set M) (_ : IsOpen U) (_ : x ∈ U)
    (α : ↥(relativeHomologyModule R n M Uᶜ)),
    ∀ (y : M) (hy : y ∈ U),
      (restrictToPoint R n M U y hy).hom α = μ y

/-- The `R`-module `Γ(M; o_M ⊗ R)` of (not-necessarily continuous) sections of the
orientation sheaf with `R`-coefficients, given here as the product of the local-homology
fibers. -/
def orientationSectionModule (R : Type) [CommRing R] (n : ℕ) (M : Type)
    [TopologicalSpace M] : ModuleCat.{0} R :=
  ModuleCat.of R (∀ x : M, ↥(localHomologyModule R n M x))

/-- The comparison map `j : H_n(M; R) → Γ(M; o_M ⊗ R)` of the Orientation Theorem,
sending a homology class to the family of its restrictions to each local-homology
fiber. -/
def orientationComparisonMap (R : Type) [CommRing R] (n : ℕ) (M : Type)
    [TopologicalSpace M] :
    relativeHomologyModule R n M ∅ →ₗ[R] (∀ x : M, ↥(localHomologyModule R n M x)) where
  toFun a x := (restrictionHomologyMap R n M ∅ {x}ᶜ (Set.empty_subset _)).hom a
  map_add' a b := funext fun x =>
    map_add (restrictionHomologyMap R n M ∅ {x}ᶜ (Set.empty_subset _)).hom a b
  map_smul' r a := funext fun x =>
    map_smul (restrictionHomologyMap R n M ∅ {x}ᶜ (Set.empty_subset _)).hom r a

end OrientationHomology
end
