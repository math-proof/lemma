module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.CupProductHelpers
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Graded.External
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part4
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct
open SingularCohomology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace SingularCohomology

open scoped Simplicial

open Opposite SimplexCategory

/-- The set of singular `n`-simplices in `X`: continuous maps `Δ^n → X`. -/
abbrev Sing (n : ℕ) (X : TopCat.{0}) : Type :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))

end SingularCohomology
