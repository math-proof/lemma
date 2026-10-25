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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section31.Part4
open Topology MulAction CategoryTheory TopologicalSpace

open CategoryTheory AlgebraicTopology SingularCohomology Limits


noncomputable section

namespace OrientationHomology

/-- (Definition 31.8) An *`R`-orientation* of an `n`-manifold `M`: a choice of
generator `μ x` in each local-homology module `H_n(M, M − {x}; R)`, depending locally
compatibly on `x`. Equivalently, a section of the unit twisted local system
`(o_M ⊗ R)^×`. -/
structure ROrientation (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (R : Type) [CommRing R] where
  μ : (x : M) → ↥(localHomologyModule R n M x)
  generates : ∀ x : M, Submodule.span R {μ x} = ⊤
  locallyCompatible : ∀ x : M, ∃ (U : Set M) (_ : IsOpen U) (_ : x ∈ U)
      (α : ↥(relativeHomologyModule R n M Uᶜ)),
      ∀ (y : M) (hy : y ∈ U),
        (restrictToPoint R n M U y hy).hom α = μ y

end OrientationHomology
end
