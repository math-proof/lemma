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
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section34.Part2
open CategoryTheory AlgebraicTopology TopologicalSpace SingularCohomology


noncomputable section

namespace CechCohomology

/-- **Transition map in the Čech directed system.**  For `U ≤ V` (i.e.
`V ⊆ U`), the inclusion `V ↪ U` induces a restriction map on singular
cochain complexes, and the resulting map on cohomology is the structure
map `cechFamily R K p U →ₗ[R] cechFamily R K p V` of the directed system
whose colimit is `cechCohomology R K p`. -/
def cechTransition (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (K : Set X) (p : ℕ) (U V : OpenNeighborhoods K) (h : U ≤ V) :
    cechFamily R K p U →ₗ[R] cechFamily R K p V :=
  (HomologicalComplex.homologyMap
    (restrictionCochainMap R (ModuleCat.of R R) (nbhdInclusion h)) p).hom

/-- **Definition 34.4 (Čech cohomology of a subset).**  The Čech
cohomology `Ȟ^p(K; R)` of a subset `K ⊂ X` with coefficients in `R` is
defined as the *directed colimit* over all open neighborhoods `U ⊇ K` of
the singular cohomologies `H^p(U; R)`, with structure maps given by
restriction along the inclusions `V ↪ U` of smaller neighborhoods.  This
agrees with the singular cohomology of `K` whenever `K` is a sufficiently
nice subset (e.g. compact ENR), via the regular-neighborhood criterion. -/
def cechCohomology (R : Type) [CommRing R]
    {X : Type} [TopologicalSpace X] (K : Set X) (p : ℕ) : ModuleCat.{0} R := by
  classical
  exact ModuleCat.of R (Module.DirectLimit (cechFamily R K p)
    (fun U V h => cechTransition R K p U V h))

end CechCohomology
end
