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
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section26.Part2
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct

open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct
open SingularCohomology


namespace SingularCohomology

open scoped Simplicial

open Opposite SimplexCategory

/-- A singular `0`-simplex in `X` is the same data as a point of `X`. -/
noncomputable def sing0EquivX (X : TopCat.{0}) : Sing 0 X ≃ X :=
  TopCat.toSSetObj₀Equiv

/-- The `0`-th face of a singular `1`-simplex (its endpoint). -/
def face₀ (X : TopCat.{0}) (σ : Sing 1 X) : Sing 0 X :=
  (TopCat.toSSet.obj X).map (SimplexCategory.δ 0).op σ

/-- The `1`-st face of a singular `1`-simplex (its starting point). -/
def face₁ (X : TopCat.{0}) (σ : Sing 1 X) : Sing 0 X :=
  (TopCat.toSSet.obj X).map (SimplexCategory.δ 1).op σ

/-- The singular `1`-simplex obtained from a path `γ : Path x y` by composing
with the canonical homeomorphism `Δ^1 ≃ [0,1]`. -/
noncomputable def oneSimplexOfPath (X : TopCat.{0}) {x y : X} (γ : Path x y) : Sing 1 X :=
  (TopCat.toSSetObjEquiv X (op ⦋1⦌)).symm
    (⟨γ ∘ stdSimplexHomeomorphUnitInterval, γ.continuous.comp
      stdSimplexHomeomorphUnitInterval.continuous⟩)

end SingularCohomology
