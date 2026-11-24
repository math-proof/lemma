module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Projection
public import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section30
open Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section30.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
section PoincareDuality

open CategoryTheory AlgebraicTopology LinearMap SingularCohomology

/-- The pairing `H^p(X; F₂) × H^q(X; F₂) → F₂` induced by cup product with a
fixed homology class `μ ∈ H_dim(X; F₂)`, given by
`(α, β) ↦ ⟨α ⌣ β, μ⟩`. Used to formulate Poincaré duality. -/
noncomputable def cupProductPairing
    (X : TopCat.{0}) (dim : ℕ) (μ : HomolZMod2 X dim)
    (p q : ℕ) (hpq : p + q = dim) :
    SingularCohomology.CohomZMod2 X p →ₗ[ZMod 2]
    SingularCohomology.CohomZMod2 X q →ₗ[ZMod 2] ZMod 2 :=
  let μ' : (singularHomologyModule (ZMod 2) X (p + q) : Type) := hpq ▸ μ
  TensorProduct.curry
    ((LinearMap.flip (kroneckerPairing (ZMod 2) X (p + q)) μ') ∘ₗ
     (cupProduct (ZMod 2) X p q).hom)


end PoincareDuality
