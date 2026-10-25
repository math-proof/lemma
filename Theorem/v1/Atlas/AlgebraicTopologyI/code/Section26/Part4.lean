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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part7
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct

open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct
open SingularCohomology


namespace SingularCohomology

open scoped Simplicial

open Opposite SimplexCategory

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- Evaluating the cochain `cochainOfFunc X N g` on a `0`-simplex `σ₀`
returns `g` evaluated at the corresponding point. -/
lemma cochainOfFunc_eval (X : TopCat.{0}) (N : ModuleCat.{0} ℤ)
    (g : X → N) (σ₀ : Sing 0 X) :
    cochainEvalN X N 0 (cochainOfFunc X N g) σ₀ = g (sing0EquivX X σ₀) := by
  simp only [cochainEvalN, cochainOfFunc]
  rw [Sigma.ι_desc]
  simp [LinearMap.toSpanSingleton_apply]

/-- Two morphisms `ℤ ⟶ N` of `ℤ`-modules that agree on `1` are equal. -/
lemma moduleCat_int_hom_ext {N : ModuleCat.{0} ℤ}
    (φ ψ : ModuleCat.of ℤ ℤ ⟶ N) (h : φ.hom (1 : ℤ) = ψ.hom (1 : ℤ)) : φ = ψ := by
  ext
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- Two `0`-cochains are equal iff they take the same value on every
singular `0`-simplex. -/
lemma cochain_ext (X : TopCat.{0}) (N : ModuleCat.{0} ℤ)
    (f₁ f₂ : (singularCochainComplex ℤ X N).X 0)
    (h : ∀ σ₀ : Sing 0 X, cochainEvalN X N 0 f₁ σ₀ = cochainEvalN X N 0 f₂ σ₀) :
    f₁ = f₂ := by
  apply Sigma.hom_ext
  intro σ₀
  exact moduleCat_int_hom_ext _ _ (h σ₀)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- A `1`-cochain vanishes iff it evaluates to zero on every singular
`1`-simplex. -/
lemma cochain1_eq_zero_iff (X : TopCat.{0}) (N : ModuleCat.{0} ℤ)
    (f : (singularCochainComplex ℤ X N).X 1) :
    f = 0 ↔ ∀ σ : Sing 1 X, cochainEvalN X N 1 f σ = 0 := by
  constructor
  · intro hf σ
    simp only [cochainEvalN, hf, Limits.HasZeroMorphisms.comp_zero]
    rfl
  · intro h
    apply Sigma.hom_ext; intro σ
    exact moduleCat_int_hom_ext _ _ (by simpa [cochainEvalN] using h σ)


end SingularCohomology
