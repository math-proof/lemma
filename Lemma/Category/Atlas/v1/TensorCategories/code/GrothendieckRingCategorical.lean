import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
open CategoryTheory MonoidalCategory Limits Finset TensorCategories CategoricalFusionData FusionCategoryBridge
open TensorCategories
open FusionRing
open CategoricalFusionData FusionRing


namespace CategoricalFusionData

/--
[basisClass_mul_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRingCategorical.lean)
-/
@[path]
lemma basisClass_mul_coeff
  [Field κ]
  {C : Type u}
  [Category.{v} C]
  [cfd : CategoricalFusionData κ C]
  {i j l : cfd.ι} :
-- imply
  (basisClass (κ := κ) (C := C) i * basisClass j).coeff l = (cfd.N i j l : ℤ) := by
-- proof
  show FusionRing.grMul (toFusionRing (κ := κ) (C := C))
    (FusionRing.basisVec i) (FusionRing.basisVec j) l = (cfd.N i j l : ℤ)
  simp only [FusionRing.grMul, FusionRing.basisVec, toFusionRing]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
end CategoricalFusionData
namespace RepZ2Categorical
open FusionRing


namespace FusionCategoryBridge

/--
[simpleClass_mul_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRingCategorical.lean)
-/
@[path]
lemma simpleClass_mul_coeff
  [Field κ]
  {C : Type u}
  [Category.{v} C]
  [cfd : CategoricalFusionData κ C]
  {i j l : cfd.ι} :
-- imply
  (simpleClass (κ := κ) (C := C) i * simpleClass j).coeff l = (cfd.N i j l : ℤ) := by
-- proof
  show grMul (toFusionRing (κ := κ) (C := C)) (basisVec i) (basisVec j) l = (cfd.N i j l : ℤ)
  simp only [grMul, basisVec, toFusionRing]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']

end FusionCategoryBridge


-- created on 2026-10-23
