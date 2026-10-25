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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section26.Part2
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct

open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct
open SingularCohomology


namespace SingularCohomology

open scoped Simplicial

open Opposite SimplexCategory

section KerD0EquivPi0

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 3200000

/-- The underlying linear map of the zeroth coboundary
`d^0 : C^0(X; N) → C^1(X; N)`. -/
abbrev d0Hom (X : TopCat.{0}) (N : ModuleCat.{0} ℤ) :=
  ((singularCochainComplex ℤ X N).sc' 0 0 1).g.hom

end KerD0EquivPi0

/-- The integral singular chain complex `C_*(X; ℤ)` of `X`. -/
abbrev singularChainZ (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  ((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X

end SingularCohomology
