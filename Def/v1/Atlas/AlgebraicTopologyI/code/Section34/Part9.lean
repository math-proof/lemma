/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section34.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section31
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
import Def.v1.Atlas.AlgebraicTopologyI.code.Section31.Part7
import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Order.Directed
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Sets.Opens
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section34
open CategoryTheory AlgebraicTopology TopologicalSpace SingularCohomology


noncomputable section

namespace CapProduct

variable (R : Type) [CommRing R]

/-- **The set of singular `n`-simplices of `X`.**  Continuous maps
`Δⁿ → X`, i.e. the `n`-cells of `Sing(X)`.  This is the underlying index
type for the free `R`-module of singular `n`-chains. -/
def cupProduct
    (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ) :
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) p : Type) →ₗ[R]
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) q : Type) →ₗ[R]
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) (p + q) : Type) :=
  TensorProduct.curry (SingularCohomology.cupProduct R X p q).hom


/-- **Generator of `H^0` of a point.**  A canonical generator of
`H^0(pt; R) ≅ R`, witnessing the rank-one freeness of the cohomology of
a point in degree 0.  This is the element whose pullback along the
unique map `X → pt` is the unit `1 ∈ H^0(X; R)` for the cup product. -/
def kroneckerPairing
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) n : Type) →ₗ[R]
    (SingularCohomology.singularHomologyModule R X n : Type) →ₗ[R] R :=
  SingularCohomology.kroneckerPairing R X n


/-- **Augmentation** `ε : H_0(X; R) → R`.  The map descended from the
chain-level augmentation `C_0(X) → R` (which collapses each 0-simplex to
`1`).  Equal to the unique map induced by `X → pt` on `H_0`, and equal
to `1 ⌢ ·` ↦ `1` via the unit relation. -/
def augmentation (R : Type) [CommRing R] (X : TopCat.{0}) :
    (SingularCohomology.singularHomologyModule R X 0 : Type) →ₗ[R] R :=
  (augmentationH0 R X).hom


/-- **Pushforward on singular homology**, `f_* : H_n(X; R) → H_n(Y; R)`.
Functoriality of singular homology in the topological space, as a
`ModuleCat`-morphism.  Used in the projection formula for the cap
product. -/
def pushforwardMap' (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    SingularCohomology.singularHomologyModule R X n ⟶
    SingularCohomology.singularHomologyModule R Y n :=
  ((singularHomologyFunctor (ModuleCat.{0} R) n).obj (ModuleCat.of R R)).map f

/-- **Pullback on singular cohomology**, `f^* : H^n(Y; R) → H^n(X; R)`.
Contravariant functoriality of singular cohomology in the topological
space.  Used in the projection formula for the cap product. -/
def pullbackMap
    (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (SingularCohomology.singularCohomology R Y (ModuleCat.of R R) n : Type) →ₗ[R]
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) n : Type) :=
  (SingularCohomology.singularCohomologyMap R f n).hom

end CapProduct
end
