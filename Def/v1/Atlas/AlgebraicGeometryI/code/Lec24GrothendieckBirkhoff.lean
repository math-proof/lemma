/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24GrothendieckBirkhoff.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Data.Multiset.Sort

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] MvPolynomial.gradedAlgebra


namespace GrothendieckBirkhoff

variable (k : Type*) [Field k]

/-- The projective line `ℙ¹_k` realised as `Proj k[x₀, x₁]`. -/
noncomputable def P1 : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)

/-- The category of `O_{ℙ¹}`-modules on `ℙ¹_k`. -/
noncomputable def ModulesP1 := (P1 k).Modules

end GrothendieckBirkhoff
