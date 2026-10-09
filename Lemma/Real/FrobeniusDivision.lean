import Mathlib
import sympy.Basic
import sympy.Algebra.Algebra.FrobeniusDivision

open FrobeniusDivision

/--
[algMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma alg_map_injective
  [DivisionRing A] [Algebra ℝ A] :
-- imply
  Function.Injective (algebraMap ℝ A) := by
-- proof
  apply algMap_injective


/--
[isIntegral_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma is_integral_mem
  [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
-- given
  (x : A) :
-- imply
  IsIntegral ℝ x := by
-- proof
  apply isIntegral_mem x


/--
[minpoly_natDegree_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma minpoly_nat_degree_le_two
  [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
-- given
  (x : A) :
-- imply
  (minpoly ℝ x).natDegree ≤ 2 := by
-- proof
  apply minpoly_natDegree_le_two x


/--
[quad_relation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma quadratic_relation
  [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
-- given
  (x : A) (hx : ∀ r : ℝ, algebraMap ℝ A r ≠ x) :
-- imply
  ∃ c₁ c₀ : ℝ, x ^ 2 + algebraMap ℝ A c₁ * x + algebraMap ℝ A c₀ = 0 := by
-- proof
  apply quad_relation hx


/--
[exists_sq_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma exists_square_eq_neg_one
  [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
-- given
  (x : A) (hx : ∀ r : ℝ, algebraMap ℝ A r ≠ x) :
-- imply
  ∃ u : A, u * u = -1 := by
-- proof
  apply exists_sq_eq_neg_one hx


/--
[complexHom_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma complex_hom_injective
  [DivisionRing A] [Algebra ℝ A]
-- given
  (f : AlgHom ℝ ℂ A) :
-- imply
  Function.Injective f := by
-- proof
  apply complexHom_injective f


/--
[surjective_of_injective_of_finrank_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma surj_of_inj_of_finrank_eq
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
-- given
  (g : E →ₗ[ℝ] F)
  (h : Module.finrank ℝ E = Module.finrank ℝ F)
  (hinj : Function.Injective g) :
-- imply
  Function.Surjective g := by
-- proof
  apply surjective_of_injective_of_finrank_eq g hinj h


/--
[equiv_real_of_finrank_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma equiv_real_of_finrank_eq_one
  [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
-- given
  (h : Module.finrank ℝ A = 1) :
-- imply
  Nonempty (AlgEquiv ℝ A ℝ) := by
-- proof
  apply equiv_real_of_finrank_one h


/--
[equiv_complex_of_finrank_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma equiv_complex_of_finrank_eq_two
  [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
-- given
  (f : AlgHom ℝ ℂ A)
  (h : Module.finrank ℝ A = 2)
  (hf : Function.Injective f) :
-- imply
  Nonempty (AlgEquiv ℝ A ℂ) := by
-- proof
  apply equiv_complex_of_finrank_two f hf h


/--
[finrank_complex_tower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma complex_tower_finrank
  [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
-- given
  (f : AlgHom ℝ ℂ A) :
-- imply
  ∃ m : ℕ, Module.finrank ℝ A = 2 * m := by
-- proof
  apply finrank_complex_tower f


/--
[field_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma finrank_of_field
  [Field K] [Algebra ℝ K] [FiniteDimensional ℝ K] :
-- imply
  Module.finrank ℝ K = 1 ∨ Module.finrank ℝ K = 2 := by
-- proof
  apply field_finrank


/--
[complexHom_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma complex_hom_apply
  [DivisionRing A] [Algebra ℝ A]
-- given
  (u : A) (hu : u * u = -1) (z : ℂ) :
-- imply
  complexHom hu z = algebraMap ℝ A z.re + z.im • u := by
-- proof
  apply complexHom_apply hu z


/--
[adjoin_pair_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma pair_adjoin_commute
  [Ring A] [Algebra ℝ A]
-- given
  (i y : A) (h : Commute i y) :
-- imply
  ∀ x ∈ Algebra.adjoin ℝ ({i, y} : Set A),
    ∀ z ∈ Algebra.adjoin ℝ ({i, y} : Set A), Commute x z := by
-- proof
  apply adjoin_pair_comm h


/--
[centralizer_eq_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma centralizer_in_range
  [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
-- given
  (i y : A) (hi : i * i = -1) (hy : y * i = i * y) :
-- imply
  y ∈ AlgHom.range (complexHom hi) := by
-- proof
  apply centralizer_eq_range hi y hy


/--
[two_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma two_ne_zero_alg
  [DivisionRing A] [Algebra ℝ A] :
-- imply
  (2 : A) ≠ 0 := by
-- proof
  apply FrobeniusDivision.two_ne_zero


/--
[eq_zero_of_add_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma zero_of_add_self_eq_zero
  [DivisionRing A] [Algebra ℝ A]
-- given
  (X : A) (h : X + X = 0) :
-- imply
  X = 0 := by
-- proof
  apply eq_zero_of_add_self h


/--
[exists_anticommute](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma exists_anticommuting
  [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
-- given
  (i w : A) (hi : i * i = -1)
  (hw : w ∉ AlgHom.range (complexHom hi)) :
-- imply
  ∃ j : A, j * j = -1 ∧ i * j + j * i = 0 := by
-- proof
  apply exists_anticommute hi hw


/--
[quatHom_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma quat_hom_injective
  [DivisionRing A] [Algebra ℝ A]
-- given
  (f : AlgHom ℝ (Quaternion ℝ) A) :
-- imply
  Function.Injective f := by
-- proof
  apply quatHom_injective f


/--
[quatHom_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma quat_hom_mk
  [DivisionRing A] [Algebra ℝ A]
-- given
  (i j : A) (hi : i * i = -1) (hj : j * j = -1)
  (hanti : i * j + j * i = 0) (a b c d : ℝ) :
-- imply
  quatHom hi hj hanti (QuaternionAlgebra.mk a b c d)
    = algebraMap ℝ A a + b • i + c • j + d • (i * j) := by
-- proof
  apply quatHom_mk hi hj hanti a b c d


/--
[comm_of_anticomm_anticomm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma anticomm_anticomm_comm
  [DivisionRing A]
-- given
  (i j a : A) (ha : i * a = -(a * i)) (hji : j * i = -(i * j)) :
-- imply
  (a * j) * i = i * (a * j) := by
-- proof
  apply comm_of_anticomm_anticomm ha hji


/--
[exists_nonreal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma exists_non_real
  [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
-- given
  (h1 : Module.finrank ℝ A ≠ 1) :
-- imply
  ∃ x : A, ∀ r : ℝ, algebraMap ℝ A r ≠ x := by
-- proof
  apply exists_nonreal h1


/--
[quatHom_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma quat_hom_surjective
  [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
-- given
  (i j : A) (hi : i * i = -1) (hj : j * j = -1)
  (hanti : i * j + j * i = 0) :
-- imply
  Function.Surjective (quatHom hi hj hanti) := by
-- proof
  apply quatHom_surjective hi hj hanti


/--
[frobenius_real_division_algebra](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/FrobeniusDivision.lean)
-/
@[path]
private lemma frobenius_real_div_algebra
  [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A] :
-- imply
  Nonempty (AlgEquiv ℝ A ℝ) ∨ Nonempty (AlgEquiv ℝ A ℂ)
    ∨ Nonempty (AlgEquiv ℝ A (Quaternion ℝ)) := by
-- proof
  apply frobenius_real_division_algebra


-- created on 2026-10-09
