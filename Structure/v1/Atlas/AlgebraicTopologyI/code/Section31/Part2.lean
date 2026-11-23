/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section31.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section32
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Lemma32_4
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section32.Part2
public import Def.v1.Atlas.AlgebraicTopologyI.code.Lemma32_4
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.RepresentationTheory.Rep.Iso
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.LocallyConstant.Basic
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section31.Part4
open Topology MulAction CategoryTheory TopologicalSpace

open CategoryTheory AlgebraicTopology SingularCohomology Limits


public noncomputable section

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
