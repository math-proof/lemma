import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private def sl2M {R : Type} [CommRing R] (s t u : R) : Matrix (Fin 2) (Fin 2) R :=
  Matrix.of (vecCons ((vecCons s (vecCons t vecEmpty))) (vecCons ((vecCons u (vecCons (-s) vecEmpty))) vecEmpty))
private lemma frob_shape_of_line {R : Type} [CommRing R] (F : Matrix (Fin 2) (Fin 2) R) (t q : R) (ht : ∀ r : R, t * r = 0 → r = 0) (hFN : F * sl2M 0 t 0 = q • (sl2M 0 t 0 * F)) : F 1 0 = 0 ∧ F 0 0 = q * F 1 1 := by
  have hL : F * sl2M 0 t 0 = Matrix.of (vecCons ((vecCons 0 (vecCons (F 0 0 * t) vecEmpty))) (vecCons ((vecCons 0 (vecCons (F 1 0 * t) vecEmpty))) vecEmpty)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two]
  have hR : q • (sl2M 0 t 0 * F) = Matrix.of (vecCons ((vecCons (q * (t * F 1 0)) (vecCons (q * (t * F 1 1)) vecEmpty))) (vecCons ((vecCons 0 (vecCons 0 vecEmpty))) vecEmpty)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul] <;> simp [sl2M]
  rw [hL, hR] at hFN
  have h11 : F 1 0 * t = 0 := congrFun (congrFun hFN 1) 1
  have h01 : F 0 0 * t = q * (t * F 1 1) := congrFun (congrFun hFN 0) 1
  have h10 : F 1 0 = 0 := ht _ (by rw [mul_comm]; apply h11)
  refine ⟨h10, ?_⟩
  have : t * (F 0 0 - q * F 1 1) = 0 := calc
    _ = F 0 0 * t - q * (t * F 1 1) := by ring
    _ = 0 := by rw [h01, sub_self]
  apply sub_eq_zero.mp (ht _ this)
/--
[Matrix_exists_adapted_frob_shape](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_exists_adapted_frob_shape.lean)
-/
@[path]
private lemma main
  {R : Type} [CommRing R] [IsDomain R]
  (N₀ P F : Matrix (Fin 2) (Fin 2) R) (hP : IsUnit P.det)
  (t : R) (ht : t ≠ 0) (hN₀P : N₀ * P = P * Matrix.of (vecCons ((vecCons 0 (vecCons t vecEmpty))) (vecCons ((vecCons 0 (vecCons 0 vecEmpty))) vecEmpty)))
  (q : R) (hFN : F * N₀ = q • (N₀ * F)) :
  -- imply
  ∃ F' : Matrix (Fin 2) (Fin 2) R,
    F * P = P * F' ∧ F' 1 0 = 0 ∧ F' 0 0 = q * F' 1 1 := by
  -- proof
  let _ := P.invertibleOfIsUnitDet hP
  have hline : Matrix.of (vecCons ((vecCons 0 (vecCons t vecEmpty))) (vecCons ((vecCons 0 (vecCons 0 vecEmpty))) vecEmpty)) = sl2M 0 t 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sl2M]
  rw [hline] at hN₀P
  have ht' : ∀ r : R, t * r = 0 → r = 0 := fun r hr => (mul_eq_zero.mp hr).resolve_left ht
  have htE : sl2M 0 t 0 = ⅟P * N₀ * P := by
    rw [Matrix.mul_assoc, hN₀P, ← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]
  have hFP : F * P = P * (⅟P * F * P) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
  have hshuffle : ∀ X Y : Matrix (Fin 2) (Fin 2) R,
      (⅟P * X * P) * (⅟P * Y * P) = ⅟P * (X * Y) * P := by
    intro X Y
    calc
      _ = ⅟P * X * (P * (⅟P * (Y * P))) := by simp only [Matrix.mul_assoc]
      _ = ⅟P * X * ((P * ⅟P) * (Y * P)) := by rw [← Matrix.mul_assoc P]
      _ = ⅟P * (X * Y) * P := by
        rw [mul_invOf_self, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
  have hF'tE : (⅟P * F * P) * sl2M 0 t 0 = q • (sl2M 0 t 0 * (⅟P * F * P)) := by
    rw [htE, hshuffle, hshuffle, hFN]
    rw [Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨h10, h00⟩ := frob_shape_of_line (⅟P * F * P) t q ht' hF'tE
  exact ⟨⅟P * F * P, hFP, h10, h00⟩


-- created on 2026-10-20
