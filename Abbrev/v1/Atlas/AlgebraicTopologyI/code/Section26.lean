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
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part2
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace SingularCohomology

/-- The $n$th singular homology module $H_n(X; R)$, as an object of `ModuleCat R`. -/
abbrev singularHomologyModule (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} R :=
  ((singularHomologyFunctor (ModuleCat.{0} R) n).obj (ModuleCat.of R R)).obj X

/-- The graded family of underlying types $n \mapsto H_n(X; R)$. -/
abbrev singularHomologyFamily (R : Type) [CommRing R]
    (X : TopCat.{0}) : ℕ → Type :=
  fun n => (singularHomologyModule R X n : Type)

/-- The total singular homology $H_*(X; R) = \bigoplus_n H_n(X; R)$ as a graded $R$-module. -/
abbrev totalSingularHomology (R : Type) [CommRing R]
    (X : TopCat.{0}) : Type :=
  DirectSum ℕ (singularHomologyFamily R X)

end SingularCohomology
end
