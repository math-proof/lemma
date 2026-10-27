import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.MultilinearExtension
open Finset BigOperators BooleanFourier


namespace BooleanFourier

/--
[multilinearExtension_eq_on_boolToReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/MultilinearExtension.lean)
-/
@[path]
lemma multilinearExtension_eq_on_boolToReal
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {b : Fin n → Bool} :
-- imply
  multilinearExtension f (fun i => boolToReal (b i)) = f b := by
-- proof
  change ∑ S : Finset (Fin n), fourierCoeff f S * chi S b = f b
  exact (fourier_expansion (f := f) (x := b)).symm

end BooleanFourier

namespace BooleanFourier

/--
[multilinearExtension_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/MultilinearExtension.lean)
-/
@[path]
lemma multilinearExtension_unique
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {coeffs : Finset (Fin n) → ℝ}
-- given
  (hagree : ∀ b : Fin n → Bool, ∑ S : Finset (Fin n), coeffs S * ∏ i ∈ S, boolToReal (b i) = f b) :
-- imply
  coeffs = fun S => fourierCoeff f S := by
-- proof
  classical
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num : (0 : ℝ) < 2) n
  have h2n_ne : (2 : ℝ) ^ n ≠ 0 := ne_of_gt h2n_pos
  funext S
  have hagree' : ∀ b : Fin n → Bool,
    ∑ T : Finset (Fin n), coeffs T * chi T b = f b := by
    intro b
    have h := hagree b
    simp only [chi]
    exact h
  have lhs_eq : (1 / (2 : ℝ) ^ n) * ∑ b : Fin n → Bool,
    (∑ T : Finset (Fin n), coeffs T * chi T b) * chi S b = coeffs S := by
    simp_rw [Finset.sum_mul]
    simp_rw [show ∀ (T : Finset (Fin n)) (b : Fin n → Bool),
      coeffs T * chi T b * chi S b = coeffs T * (chi T b * chi S b) from
      fun T b => by ring]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ (α := Fin n → Bool))]
    simp_rw [← Finset.mul_sum]
    simp_rw [sum_chi_mul_chi_eq]
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    field_simp
  have rhs_eq : (1 / (2 : ℝ) ^ n) * ∑ b : Fin n → Bool,
    (∑ T : Finset (Fin n), coeffs T * chi T b) * chi S b = fourierCoeff f S := by
    simp only [fourierCoeff]
    congr 1
    exact Finset.sum_congr rfl (fun b _ => by
      rw [hagree' b])
  linarith [lhs_eq, rhs_eq]

end BooleanFourier

namespace BooleanFourier

/--
[multilinearExtension_unique'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/MultilinearExtension.lean)
-/
@[path]
lemma multilinearExtension_unique'
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {coeffs : Finset (Fin n) → ℝ}
  {x : Fin n → ℝ}
-- given
  (hagree : ∀ b : Fin n → Bool, ∑ S : Finset (Fin n), coeffs S * ∏ i ∈ S, boolToReal (b i) = f b) :
-- imply
  ∑ S : Finset (Fin n), coeffs S * ∏ i ∈ S, x i = multilinearExtension f x := by
-- proof
  simp only [multilinearExtension]
  congr 1; ext S; congr 1
  exact congr_fun (multilinearExtension_unique f coeffs hagree) S

end BooleanFourier


-- created on 2026-10-23
-- updated on 2026-10-27
