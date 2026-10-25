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
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section34
open CategoryTheory AlgebraicTopology TopologicalSpace SingularCohomology


noncomputable section

namespace CechCohomology

/-- **Neighborhood-retract property** of a subset `X ⊂ ℝⁿ`.  `X` is a
neighborhood retract when there exists an open neighborhood `U ⊇ X` and a
continuous retraction `r : U → X` (i.e. `r` restricted to `X` is the
identity).  Compact ANRs in `ℝⁿ` (in particular all compact topological
manifolds and CW complexes) have this property, which is the geometric
input that lets the Čech cohomology of `X` be computed by the singular
cohomology of a neighborhood. -/
def IsNeighborhoodRetract {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (U : Set (EuclideanSpace ℝ (Fin n))) (_ : IsOpen U) (hXU : X ⊆ U)
    (r : ↥U → ↥X), Continuous r ∧ ∀ (x : ↥X), r ⟨x.1, hXU x.2⟩ = x

/-- **Inclusion of one neighborhood into a larger one.**  For two open
neighborhoods `U ≤ V` of `K` (so `V ⊆ U` in the reverse-inclusion
convention), the underlying-set inclusion `V ↪ U` is a morphism in `TopCat`.
This is the morphism whose restriction induces the structure map in the
directed system of cochain complexes used to define Čech cohomology. -/
def nbhdInclusion {X : Type*} [TopologicalSpace X] {K : Set X}
    {U V : OpenNeighborhoods K} (h : U ≤ V) : TopCat.of ↥V.1.1 ⟶ TopCat.of ↥U.1.1 :=
  ⟨fun x => ⟨x.1, h x.2⟩, continuous_inclusion h⟩

/-- **Singular cohomology of a neighborhood `U` of `K`** in degree `p`,
with coefficients in `R`, packaged as a `ModuleCat R`.  This is the
typewise object that lives at index `U` in the directed system whose
colimit defines `cechCohomology R K p`. -/
def nbhdSingCohom (R : Type) [CommRing R] {X : Type} [TopologicalSpace X] {K : Set X}
    (U : OpenNeighborhoods K) (p : ℕ) : ModuleCat.{0} R :=
  singularCohomology R (TopCat.of ↥U.1.1) (ModuleCat.of R R) p

/-- The underlying-type version of `nbhdSingCohom`, used so that the
direct-limit machinery (which works on plain types with `Module` structure)
can be applied to the family `U ↦ H^p(U; R)`. -/
def cechFamily (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (K : Set X) (p : ℕ) (U : OpenNeighborhoods K) : Type :=
  (nbhdSingCohom R U p : Type _)

end CechCohomology
end
