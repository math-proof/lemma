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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part6
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct

open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct
open SingularCohomology


namespace SingularCohomology

open scoped Simplicial

open Opposite SimplexCategory

section CoboundaryFormula

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 3200000

/-- Boundary formula for a singular `1`-simplex: `∂σ = face₀(σ) − face₁(σ)`. -/
lemma singularChainZ_ι_comp_d (X : TopCat.{0}) (σ : Sing 1 X) :
    Sigma.ι (fun (_ : Sing 1 X) => ModuleCat.of ℤ ℤ) σ ≫
      (singularChainZ X).d 1 0 =
    Sigma.ι (fun (_ : Sing 0 X) => ModuleCat.of ℤ ℤ) (face₀ X σ) -
    Sigma.ι (fun (_ : Sing 0 X) => ModuleCat.of ℤ ℤ) (face₁ X σ) := by
  simp only [singularChainZ, singularChainComplexFunctor, SSet.singularChainComplexFunctor]
  dsimp only [Functor.comp_obj, Functor.comp_map,
    Functor.whiskeringLeft, Functor.postcompose₂]
  erw [AlternatingFaceMapComplex.obj_d_eq]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    SimplicialObject.δ, sub_eq_add_neg]
  erw [Sigma.ι_comp_map' _ _ σ, Sigma.ι_comp_map' _ _ σ]
  simp only [Category.id_comp, face₀, face₁]

/-- Dual formula: for a `0`-cochain `f`, the value of `d^0 f` on a singular
`1`-simplex `σ` is `f(face₀ σ) − f(face₁ σ)`. -/
lemma coboundary_zero_eval (X : TopCat.{0}) (N : ModuleCat.{0} ℤ)
    (f : (singularCochainComplex ℤ X N).X 0)
    (σ : Sing 1 X) :
    cochainEvalN X N 1 ((singularCochainComplex ℤ X N).d 0 1 f) σ =
    cochainEvalN X N 0 f (face₀ X σ) - cochainEvalN X N 0 f (face₁ X σ) := by
  simp only [cochainEvalN]
  erw [show (Sigma.ι (fun _ => ModuleCat.of ℤ ℤ) σ ≫
      (singularChainZ X).d 1 0 ≫ f).hom (1 : ℤ) =
    ((Sigma.ι _ σ ≫ (singularChainZ X).d 1 0) ≫ f).hom (1 : ℤ) from by
      rw [Category.assoc]]
  rw [singularChainZ_ι_comp_d]
  simp only [Preadditive.sub_comp, ModuleCat.hom_sub, LinearMap.sub_apply]

end CoboundaryFormula
end SingularCohomology
