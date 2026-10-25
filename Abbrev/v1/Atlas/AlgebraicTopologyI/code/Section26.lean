/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.CupProductHelpers
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Graded.External
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part2
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct


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
