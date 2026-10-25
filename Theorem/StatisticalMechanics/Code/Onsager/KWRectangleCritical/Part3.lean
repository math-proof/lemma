/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.KWSpectralCritical
import Def.StatisticalMechanics.Code.Onsager.KWRectangleCritical.Part4


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


theorem ons_arrivalTurnMatrixOf_isHermitian (S : Type*) [DecidableEq S] :
    (ons_arrivalTurnMatrixOf S).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext ⟨p2, nu⟩ ⟨p1, mu⟩
  simp only [Matrix.conjTranspose_apply]
  by_cases h : p1 = p2
  · subst p2
    fin_cases mu <;> fin_cases nu <;>
      simp [ons_arrivalTurnMatrixOf, ons_turnMatrix, ons_turnW,
        ons_turnRoot_conj]
  · simp [ons_arrivalTurnMatrixOf, h, Ne.symm h]

theorem ons_arrivalTurnMatrixOf_centered_apply (S : Type*) [DecidableEq S]
    (d2 d1 : S × Fin 4) :
    (ons_arrivalTurnMatrixOf S - 1) d2 d1 =
      if d2.1 = d1.1 then
        (ons_turnMatrix ons_turnRoot - 1) d2.2 d1.2 else 0 := by
  by_cases hsite : d2.1 = d1.1
  · simp [ons_arrivalTurnMatrixOf, Matrix.one_apply, hsite, Prod.ext_iff]
  · have hdart : d2 ≠ d1 := fun h => hsite (congrArg Prod.fst h)
    simp [ons_arrivalTurnMatrixOf, hsite, hdart]

theorem ons_arrivalTurnMatrixOf_centered_sq (S : Type*)
    [Fintype S] [DecidableEq S] :
    (ons_arrivalTurnMatrixOf S - 1) *
        (ons_arrivalTurnMatrixOf S - 1) =
      (2 : Complex) • (1 : Matrix (S × Fin 4) (S × Fin 4) Complex) := by
  ext ⟨p2, nu⟩ ⟨p1, mu⟩
  simp only [Matrix.mul_apply, ons_arrivalTurnMatrixOf_centered_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single p2]
  · have hlocal := congrFun (congrFun ons_turnMatrix_centered_sq nu) mu
    by_cases hsite : p2 = p1
    · subst p1
      simpa [Matrix.mul_apply, Matrix.one_apply] using hlocal
    · have hdart : (p2, nu) ≠ (p1, mu) :=
        fun h => hsite (congrArg Prod.fst h)
      simp [hsite, hdart]
  · intro p _ hp
    simp [Ne.symm hp]
  · simp

theorem norm_ons_arrivalTurnMatrixOf_centered (S : Type*)
    [Fintype S] [DecidableEq S] [Nonempty S] :
    letI : NormedRing (Matrix (S × Fin 4) (S × Fin 4) Complex) :=
      Matrix.instL2OpNormedRing
    ‖ons_arrivalTurnMatrixOf S - 1‖ = Real.sqrt 2 := by
  letI : NormedRing (Matrix (S × Fin 4) (S × Fin 4) Complex) :=
    Matrix.instL2OpNormedRing
  let B := ons_arrivalTurnMatrixOf S - 1
  have hBstar : Bᴴ = B := by
    dsimp [B]
    rw [Matrix.conjTranspose_sub, (ons_arrivalTurnMatrixOf_isHermitian S).eq,
      Matrix.conjTranspose_one]
  have hsq : B * B =
      (2 : Complex) • (1 : Matrix (S × Fin 4) (S × Fin 4) Complex) :=
    ons_arrivalTurnMatrixOf_centered_sq S
  have hnormsq : ‖B‖ * ‖B‖ = 2 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hBstar, hsq]
    norm_num
  have hsqrt : 0 <= Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by norm_num
  nlinarith [norm_nonneg B]

theorem norm_ons_arrivalTurnMatrixOf_le (S : Type*)
    [Fintype S] [DecidableEq S] [Nonempty S] :
    letI : NormedRing (Matrix (S × Fin 4) (S × Fin 4) Complex) :=
      Matrix.instL2OpNormedRing
    ‖ons_arrivalTurnMatrixOf S‖ <= Real.sqrt 2 + 1 := by
  letI : NormedRing (Matrix (S × Fin 4) (S × Fin 4) Complex) :=
    Matrix.instL2OpNormedRing
  calc
    ‖ons_arrivalTurnMatrixOf S‖ =
        ‖(ons_arrivalTurnMatrixOf S - 1) + 1‖ := by rw [sub_add_cancel]
    _ <= ‖ons_arrivalTurnMatrixOf S - 1‖ +
        ‖(1 : Matrix (S × Fin 4) (S × Fin 4) Complex)‖ := norm_add_le _ _
    _ = Real.sqrt 2 + 1 := by
      rw [norm_ons_arrivalTurnMatrixOf_centered]
      simp


theorem norm_sq_arrivalTurnMatrixOf_centered_apply (S : Type*)
    [Fintype S] [DecidableEq S] [Nonempty S]
    (z : EuclideanSpace Complex (S × Fin 4)) :
    let B := ons_arrivalTurnMatrixOf S - 1
    ‖Matrix.toEuclideanCLM (n := S × Fin 4) (𝕜 := Complex) B z‖ ^ 2 =
      2 * ‖z‖ ^ 2 := by
  let B := ons_arrivalTurnMatrixOf S - 1
  let T := Matrix.toEuclideanCLM (n := S × Fin 4) (𝕜 := Complex) B
  have h := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left T z
  have hadj : ContinuousLinearMap.adjoint T =
      Matrix.toEuclideanCLM (n := S × Fin 4) (𝕜 := Complex) Bᴴ := by
    dsimp [T]
    exact (map_star (Matrix.toEuclideanCLM
      (n := S × Fin 4) (𝕜 := Complex)) B).symm
  rw [show (ContinuousLinearMap.adjoint T) ∘L T =
      Matrix.toEuclideanCLM (n := S × Fin 4) (𝕜 := Complex) (Bᴴ * B) by
    rw [hadj]
    exact (map_mul (Matrix.toEuclideanCLM
      (n := S × Fin 4) (𝕜 := Complex)) Bᴴ B).symm] at h
  have hstar : Bᴴ = B := by
    dsimp [B]
    rw [Matrix.conjTranspose_sub,
      (ons_arrivalTurnMatrixOf_isHermitian S).eq, Matrix.conjTranspose_one]
  have hsq : Bᴴ * B =
      (2 : Complex) • (1 : Matrix (S × Fin 4) (S × Fin 4) Complex) := by
    rw [hstar]
    exact ons_arrivalTurnMatrixOf_centered_sq S
  rw [hsq] at h
  change ‖T z‖ ^ 2 = 2 * ‖z‖ ^ 2
  calc
    ‖T z‖ ^ 2 = 2 * (↑(‖z‖ ^ 2) : Complex).re := by
      simpa [inner_smul_left] using h
    _ = 2 * ‖z‖ ^ 2 := by norm_cast


theorem arrivalTurnMatrixOf_apply_eq_of_norm_eq (S : Type*)
    [Fintype S] [DecidableEq S] [Nonempty S]
    (z : EuclideanSpace Complex (S × Fin 4))
    (hnorm : ‖Matrix.toEuclideanCLM
        (n := S × Fin 4) (𝕜 := Complex) (ons_arrivalTurnMatrixOf S) z‖ =
      (Real.sqrt 2 + 1) * ‖z‖) :
    Matrix.toEuclideanCLM
        (n := S × Fin 4) (𝕜 := Complex) (ons_arrivalTurnMatrixOf S) z =
      ((Real.sqrt 2 + 1 : Real) : Complex) • z := by
  let R := Matrix.toEuclideanCLM
    (n := S × Fin 4) (𝕜 := Complex) (ons_arrivalTurnMatrixOf S)
  let B := Matrix.toEuclideanCLM
    (n := S × Fin 4) (𝕜 := Complex) (ons_arrivalTurnMatrixOf S - 1)
  have hBsq : ‖B z‖ ^ 2 = 2 * ‖z‖ ^ 2 :=
    norm_sq_arrivalTurnMatrixOf_centered_apply S z
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hBnorm : ‖B z‖ = Real.sqrt 2 * ‖z‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [hBsq, mul_pow, hsqrt_sq]
  have hR : R z = z + B z := by
    dsimp [R, B]
    rw [map_sub]
    simp
  have htri : ‖z + B z‖ = ‖z‖ + ‖B z‖ := by
    rw [← hR, hnorm, hBnorm]
    ring
  have haddsq := norm_add_sq (𝕜 := Complex) z (B z)
  rw [htri] at haddsq
  have hinner : RCLike.re (inner Complex z (B z)) =
      Real.sqrt 2 * ‖z‖ ^ 2 := by
    rw [hBnorm] at haddsq
    ring_nf at haddsq
    have htwo : RCLike.re (inner Complex z (B z)) * 2 =
        ‖z‖ ^ 2 * Real.sqrt 2 * 2 := by
      calc
        RCLike.re (inner Complex z (B z)) * 2 =
            (‖z‖ ^ 2 + ‖z‖ ^ 2 * Real.sqrt 2 ^ 2 +
              RCLike.re (inner Complex z (B z)) * 2) -
              ‖z‖ ^ 2 - ‖z‖ ^ 2 * Real.sqrt 2 ^ 2 := by ring
        _ = (‖z‖ ^ 2 + ‖z‖ ^ 2 * Real.sqrt 2 * 2 +
              ‖z‖ ^ 2 * Real.sqrt 2 ^ 2) -
              ‖z‖ ^ 2 - ‖z‖ ^ 2 * Real.sqrt 2 ^ 2 := by rw [haddsq]
        _ = ‖z‖ ^ 2 * Real.sqrt 2 * 2 := by ring
    nlinarith only [htwo]
  have heq : B z = (Real.sqrt 2 : Complex) • z := by
    have hinner' : (inner Complex z (B z)).re =
        Real.sqrt 2 * ‖z‖ ^ 2 := by
      simpa only [RCLike.re_to_complex] using hinner
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := Complex)
    · rw [hBnorm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    · rw [inner_smul_right, ← inner_conj_symm, RCLike.mul_re,
        RCLike.conj_re, RCLike.conj_im]
      simp only [RCLike.re_to_complex, RCLike.im_to_complex,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [hinner', norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
      nlinarith [hsqrt_sq]
  rw [hR, heq]
  module


end StatMech.Onsager
