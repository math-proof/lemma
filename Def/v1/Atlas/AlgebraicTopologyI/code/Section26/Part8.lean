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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section26.Part4
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct

open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct
open SingularCohomology


namespace SingularCohomology

open scoped Simplicial

open Opposite SimplexCategory

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- A `0`-cocycle is the same data as a function `X → N` that is constant
on path components. This is the key linear equivalence underlying
`H^0(X; N) ≅ Map(π₀(X), N)`. -/
noncomputable def kerD0EquivPathConstant (X : TopCat.{0}) (N : ModuleCat.{0} ℤ) :
    LinearMap.ker (d0Hom X N) ≃ₗ[ℤ] pathConstantSubmodule X N where

  toFun := fun ⟨f, hf⟩ =>
    ⟨fun x => cochainEvalN X N 0 f ((sing0EquivX X).symm x),
     fun x y hxy => by
       obtain ⟨γ⟩ := hxy
       have hker : d0Hom X N f = 0 := by rwa [LinearMap.mem_ker] at hf
       let σ := oneSimplexOfPath X γ
       have hσ : cochainEvalN X N 0 f (face₀ X σ) =
           cochainEvalN X N 0 f (face₁ X σ) := by
         have hcb := coboundary_zero_eval X N f σ
         have hzero : cochainEvalN X N 1 ((singularCochainComplex ℤ X N).d 0 1 f) σ = 0 := by
           rw [show (singularCochainComplex ℤ X N).d 0 1 f = d0Hom X N f from rfl, hker]
           simp [cochainEvalN]
         rw [hzero] at hcb
         exact sub_eq_zero.mp hcb.symm
       show cochainEvalN X N 0 f ((sing0EquivX X).symm x) =
            cochainEvalN X N 0 f ((sing0EquivX X).symm y)
       conv_lhs => rw [show (sing0EquivX X).symm x = face₁ X σ from by
             rw [Equiv.symm_apply_eq]; exact (face₁_oneSimplexOfPath X γ).symm]
       conv_rhs => rw [show (sing0EquivX X).symm y = face₀ X σ from by
             rw [Equiv.symm_apply_eq]; exact (face₀_oneSimplexOfPath X γ).symm]
       exact hσ.symm⟩

  invFun := fun ⟨g, hg⟩ =>
    ⟨cochainOfFunc X N g, by
       rw [LinearMap.mem_ker]
       rw [show d0Hom X N (cochainOfFunc X N g) =
           (singularCochainComplex ℤ X N).d 0 1 (cochainOfFunc X N g) from rfl]
       rw [cochain1_eq_zero_iff]
       intro σ
       rw [coboundary_zero_eval]
       rw [cochainOfFunc_eval, cochainOfFunc_eval]
       have := joined_of_one_simplex X σ
       rw [hg _ _ this]
       simp⟩

  left_inv := fun ⟨f, hf⟩ => by
    simp only
    congr 1
    apply cochain_ext
    intro σ₀
    simp only [cochainOfFunc_eval]
    congr 1
    exact (sing0EquivX X).symm_apply_apply σ₀

  right_inv := fun ⟨g, hg⟩ => by
    simp only
    simp_rw [cochainOfFunc_eval, Equiv.apply_symm_apply]
  map_add' := fun ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ => by simp only; rfl
  map_smul' := fun c ⟨f, hf⟩ => by simp only; rfl

/-- Composing the kernel-vs-path-constant equivalence with the
path-constant-vs-`π₀` equivalence: `ker(d^0) ≃ Map(π₀(X), N)`. -/
noncomputable def singularCohomologyKerEquivPi0Map (X : TopCat.{0}) (N : ModuleCat.{0} ℤ) :
    LinearMap.ker (d0Hom X N) ≃ₗ[ℤ] (ZerothHomotopy X → N) :=
  (kerD0EquivPathConstant X N).trans (pathConstantEquivPi0Func X N)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- Lemma 26.6: the zeroth singular cohomology with coefficients in `N`
is naturally isomorphic to the module of functions from `π₀(X)` to `N`. -/
noncomputable def singularCohomology_zero_eq_map_pi0
    (X : TopCat.{0}) (N : ModuleCat.{0} ℤ) :
    singularCohomology ℤ X N 0 ≅ ModuleCat.of ℤ (ZerothHomotopy X → N) := by
  refine (singularCohomologyZeroIsoKer X N).trans ?_
  convert (singularCohomologyKerEquivPi0Map X N).toModuleIso using 1
  · congr 1; exact Subsingleton.elim _ _

end SingularCohomology
