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
public import Instance.v1.Atlas.AlgebraicTopologyI.code.Section30
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

/-- Singular cohomology with coefficients in `F₂ = ZMod 2`, as a type. -/
abbrev SingularCohomology.CohomZMod2 (X : TopCat.{0}) (n : ℕ) : Type :=
  (singularCohomology (ZMod 2) X (ModuleCat.of (ZMod 2) (ZMod 2)) n : Type)

/-- Singular homology with coefficients in `F₂ = ZMod 2`, as a type. -/
abbrev HomolZMod2 (X : TopCat.{0}) (n : ℕ) : Type :=
  (singularHomologyModule (ZMod 2) X n : Type)

end PoincareDuality
