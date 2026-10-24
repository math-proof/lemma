import Mathlib
import sympy.Basic
open scoped InnerProductSpace


namespace MetaMathlibExt

/--
[deGua_dist01](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/DeGuaHeron.lean)
-/
@[path]
private lemma deGua_dist01 (a b : ℝ) :
  dist (EuclideanSpace.single (0 : Fin 3) a)
    (EuclideanSpace.single (1 : Fin 3) b) ^ 2 = a ^ 2 + b ^ 2 := by
  rw [dist_eq_norm, norm_sub_sq_real]
  have h01ne : (0 : Fin 3) ≠ 1 := by decide
  have e1 : ⟪EuclideanSpace.single (0 : Fin 3) a,
    EuclideanSpace.single (1 : Fin 3) b⟫_ℝ = 0 := by
    rw [EuclideanSpace.inner_single_left, RCLike.conj_to_real, PiLp.single_apply,
      ite_eq_right h01ne, mul_zero]
  have n0 : ‖EuclideanSpace.single (0 : Fin 3) a‖ ^ 2 = a ^ 2 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  have n1 : ‖EuclideanSpace.single (1 : Fin 3) b‖ ^ 2 = b ^ 2 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  rw [e1, n0, n1]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[deGua_dist12](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/DeGuaHeron.lean)
-/
@[path]
private lemma deGua_dist12 (b c : ℝ) :
  dist (EuclideanSpace.single (1 : Fin 3) b)
    (EuclideanSpace.single (2 : Fin 3) c) ^ 2 = b ^ 2 + c ^ 2 := by
  rw [dist_eq_norm, norm_sub_sq_real]
  have h12ne : (1 : Fin 3) ≠ 2 := by decide
  have e1 : ⟪EuclideanSpace.single (1 : Fin 3) b,
    EuclideanSpace.single (2 : Fin 3) c⟫_ℝ = 0 := by
    rw [EuclideanSpace.inner_single_left, RCLike.conj_to_real, PiLp.single_apply,
      ite_eq_right h12ne, mul_zero]
  have n0 : ‖EuclideanSpace.single (1 : Fin 3) b‖ ^ 2 = b ^ 2 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  have n1 : ‖EuclideanSpace.single (2 : Fin 3) c‖ ^ 2 = c ^ 2 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  rw [e1, n0, n1]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[deGua_dist20](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/DeGuaHeron.lean)
-/
@[path]
private lemma deGua_dist20 (c a : ℝ) :
  dist (EuclideanSpace.single (2 : Fin 3) c)
    (EuclideanSpace.single (0 : Fin 3) a) ^ 2 = c ^ 2 + a ^ 2 := by
  rw [dist_eq_norm, norm_sub_sq_real]
  have h20ne : (2 : Fin 3) ≠ 0 := by decide
  have e1 : ⟪EuclideanSpace.single (2 : Fin 3) c,
    EuclideanSpace.single (0 : Fin 3) a⟫_ℝ = 0 := by
    rw [EuclideanSpace.inner_single_left, RCLike.conj_to_real, PiLp.single_apply,
      ite_eq_right h20ne, mul_zero]
  have n0 : ‖EuclideanSpace.single (2 : Fin 3) c‖ ^ 2 = c ^ 2 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  have n1 : ‖EuclideanSpace.single (0 : Fin 3) a‖ ^ 2 = a ^ 2 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  rw [e1, n0, n1]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[deGua_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/DeGuaHeron.lean)
-/
@[path]
lemma deGua_theorem
  :
-- imply
  ∀ (a b c A : ℝ),
    let p₀ := by
-- proof
  intro a b c A p₀ p₁ p₂ s _ _ _ hA
  have e0 : p₀ = EuclideanSpace.single (0 : Fin 3) a := rfl
  have e1 : p₁ = EuclideanSpace.single (1 : Fin 3) b := rfl
  have e2 : p₂ = EuclideanSpace.single (2 : Fin 3) c := rfl
  have es : s = (dist p₀ p₁ + dist p₁ p₂ + dist p₂ p₀) / 2 := rfl
  have h01 : dist p₀ p₁ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [e0, e1]; exact deGua_dist01 a b
  have h12 : dist p₁ p₂ ^ 2 = b ^ 2 + c ^ 2 := by
    rw [e1, e2]; exact deGua_dist12 b c
  have h20 : dist p₂ p₀ ^ 2 = c ^ 2 + a ^ 2 := by
    rw [e2, e0]; exact deGua_dist20 c a
  have d01nn : 0 ≤ dist p₀ p₁ := dist_nonneg
  have d12nn : 0 ≤ dist p₁ p₂ := dist_nonneg
  have d20nn : 0 ≤ dist p₂ p₀ := dist_nonneg
  have t1 : dist p₀ p₁ ≤ dist p₀ p₂ + dist p₂ p₁ := dist_triangle _ _ _
  have t2 : dist p₁ p₂ ≤ dist p₁ p₀ + dist p₀ p₂ := dist_triangle _ _ _
  have t3 : dist p₂ p₀ ≤ dist p₂ p₁ + dist p₁ p₀ := dist_triangle _ _ _
  have c01 : dist p₁ p₀ = dist p₀ p₁ := dist_comm _ _
  have c12 : dist p₂ p₁ = dist p₁ p₂ := dist_comm _ _
  have c20 : dist p₀ p₂ = dist p₂ p₀ := dist_comm _ _
  have hsnn : 0 ≤ s := by rw [es]; linarith
  have hs01 : 0 ≤ s - dist p₀ p₁ := by rw [es]; linarith
  have hs12 : 0 ≤ s - dist p₁ p₂ := by rw [es]; linarith
  have hs20 : 0 ≤ s - dist p₂ p₀ := by rw [es]; linarith
  have hH : 0 ≤ s * ((s - dist p₀ p₁) * ((s - dist p₁ p₂) * (s - dist p₂ p₀))) :=
    mul_nonneg hsnn (mul_nonneg hs01 (mul_nonneg hs12 hs20))
  have hAsq : A ^ 2
    = s * ((s - dist p₀ p₁) * ((s - dist p₁ p₂) * (s - dist p₂ p₀))) := by
    rw [hA, Real.sq_sqrt hH]
  have key : 16 * (s * ((s - dist p₀ p₁) * ((s - dist p₁ p₂) * (s - dist p₂ p₀))))
    = 2 * ((dist p₀ p₁ ^ 2) * (dist p₁ p₂ ^ 2) + (dist p₁ p₂ ^ 2) * (dist p₂ p₀ ^ 2)
      + (dist p₂ p₀ ^ 2) * (dist p₀ p₁ ^ 2))
      - ((dist p₀ p₁ ^ 2) ^ 2 + (dist p₁ p₂ ^ 2) ^ 2
        + (dist p₂ p₀ ^ 2) ^ 2) := by
    rw [es]; ring
  rw [h01, h12, h20] at key
  have hHval : s * ((s - dist p₀ p₁) * ((s - dist p₁ p₂) * (s - dist p₂ p₀)))
    = (a * b / 2) ^ 2 + (b * c / 2) ^ 2 + (c * a / 2) ^ 2 := by
    linear_combination key / 16
  rwa [hAsq]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
