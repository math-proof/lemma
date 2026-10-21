import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
private lemma aux_field {K : Type*} [Field K] (d : κ → K) (c : K) (hd : ∀ i, d i ≠ 0) :
    (Matrix.of fun i j => (if i = j then d i else 0) + c).det =
      (∏ i, d i) + c * ∑ i, ∏ j ∈ Finset.univ.erase i, d j := by
  set R : Matrix κ κ K := Matrix.of fun i _ => c / d i with hR
  have hfactor : (Matrix.of fun i j => (if i = j then d i else 0) + c)
      = Matrix.diagonal d * (1 + R) := by
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.add_apply, Matrix.one_apply, hR,
      Matrix.of_apply, mul_add, mul_ite, mul_one, mul_zero,
      mul_div_cancel₀ c (hd i)]
  have hRrank1 : R = Matrix.replicateCol Unit (fun i => c / d i)
      * Matrix.replicateRow Unit (1 : κ → K) := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_unique]
    simp only [hR, Matrix.of_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply,
      Pi.one_apply, mul_one]
  have hdet : (1 + R).det = 1 + ∑ i, c / d i := by
    rw [hRrank1, Matrix.det_one_add_mul_comm, Matrix.det_unique, Matrix.add_apply,
      Matrix.one_apply_eq, Matrix.mul_apply]
    simp only [Matrix.replicateRow_apply, Matrix.replicateCol_apply, Pi.one_apply, one_mul]
  rw [hfactor, Matrix.det_mul, Matrix.det_diagonal, hdet, mul_add, mul_one,
    Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)]
  field_simp [hd i]
/--
[Matrix_det_diagonal_add_const_int](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_det_diagonal_add_const_int.lean)
-/
@[path]
private lemma main {κ : Type*} [Fintype κ] [DecidableEq κ] (d : κ → ℤ) (c : ℤ)
    (hd : ∀ i, d i ≠ 0) :
    (Matrix.of fun i j => (if i = j then d i else 0) + c).det =
      (∏ i, d i) + c * ∑ i, ∏ j ∈ Finset.univ.erase i, d j := by
  have hQ := aux_field (K := ℚ) (fun i => (d i : ℚ)) (c : ℚ)
    (fun i => Int.cast_ne_zero.mpr (hd i))
  have hmap : ((Matrix.of fun i j => (if i = j then d i else 0) + c).map
      (Int.cast : ℤ → ℚ)).det
        = ((Matrix.of fun i j => (if i = j then d i else 0) + c).det : ℚ) :=
    (RingHom.map_det (Int.castRingHom ℚ) _).symm
  have hmat : (Matrix.of fun i j => (if i = j then d i else 0) + c).map
      (Int.cast : ℤ → ℚ)
        = Matrix.of fun i j => (if i = j then ((d i : ℚ)) else 0) + (c : ℚ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> push_cast <;> ring
  apply Int.cast_injective (α := ℚ)
  rw [← hmap, hmat, hQ]
  push_cast
  ring

-- created on 2026-10-20
