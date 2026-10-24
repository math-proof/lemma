import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private abbrev M2 (a b c d : α) : Matrix (Fin 2) (Fin 2) α :=
  Matrix.of (Matrix.vecCons (Matrix.vecCons a (Matrix.vecCons b Matrix.vecEmpty)) (Matrix.vecCons (Matrix.vecCons c (Matrix.vecCons d Matrix.vecEmpty)) Matrix.vecEmpty))

/--
[Matrix_exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul.lean)
-/
@[path]
private lemma main
  (q : ℕ) (k : Type) [Field k] (φ : ZMod q →+* k)
  (B : Matrix (Fin 2) (Fin 2) k) (hB : B.det ≠ 0)
  (h : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) (ZMod q), ∃ c : k, B * (γ : Matrix (Fin 2) (Fin 2) (ZMod q)).map φ = c • ((γ : Matrix (Fin 2) (Fin 2) (ZMod q)).map φ * B)) :
  -- imply
  ∃ a : k, B = a • (1 : Matrix (Fin 2) (Fin 2) k) := by
  -- proof
  let u : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) := ⟨M2 1 1 0 1, by simp [Matrix.det_fin_two_of]⟩
  let v : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) := ⟨M2 1 0 1 1, by simp [Matrix.det_fin_two_of]⟩
  have hu : ((u : Matrix (Fin 2) (Fin 2) (ZMod q)).map φ) = M2 (1 : k) 1 0 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [u]
  have hv : ((v : Matrix (Fin 2) (Fin 2) (ZMod q)).map φ) = M2 (1 : k) 0 1 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [v]
  obtain ⟨c, hc⟩ := h u
  obtain ⟨c', hc'⟩ := h v
  rw [hu] at hc
  rw [hv] at hc'
  set a := B 0 0 with ha
  set b := B 0 1 with hb
  set p := B 1 0 with hp
  set d := B 1 1 with hd
  have hBe : B = M2 a b p d := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hdet : a * d - b * p ≠ 0 := by
    rw [hBe, Matrix.det_fin_two_of] at hB
    apply hB
  rw [hBe] at hc hc'
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e10 := congrFun (congrFun hc 1) 0
  have e11 := congrFun (congrFun hc 1) 1
  have f00 := congrFun (congrFun hc' 0) 0
  have f01 := congrFun (congrFun hc' 0) 1
  have f10 := congrFun (congrFun hc' 1) 0
  have f11 := congrFun (congrFun hc' 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] at e00 e01 e10 e11 f00 f01 f10 f11
  have hp0 : p = 0 := by
    by_contra hp'
    have hc1 : c = 1 := by
      have : (c - 1) * p = 0 := by linear_combination (-1 : k) * e10
      obtain h1 | h1 := mul_eq_zero.mp this
      ·
        linear_combination h1
      ·
        apply absurd h1 hp'
    subst hc1
    apply hp'
    linear_combination (-1 : k) * e00
  have had : a = d := by
    if hc1 : c = 1 then
      subst hc1
      linear_combination e01
    else
      exfalso
      have ha0 : a = 0 := by
        have : (c - 1) * a = 0 := by linear_combination (-1 : k) * e00 + (-c) * hp0
        obtain h1 | h1 := mul_eq_zero.mp this
        ·
          apply absurd (by linear_combination h1) hc1
        ·
          apply h1
      have hd0 : d = 0 := by
        have : (c - 1) * d = 0 := by linear_combination (-1 : k) * e11 + hp0
        obtain h1 | h1 := mul_eq_zero.mp this
        ·
          apply absurd (by linear_combination h1) hc1
        ·
          apply h1
      apply hdet
      rw [ha0, hd0, hp0]
      ring
  have hb0 : b = 0 := by
    by_contra hb'
    have hc1 : c' = 1 := by
      have : (c' - 1) * b = 0 := by linear_combination (-1 : k) * f01
      obtain h1 | h1 := mul_eq_zero.mp this
      ·
        linear_combination h1
      ·
        apply absurd h1 hb'
    subst hc1
    apply hb'
    linear_combination f00
  refine ⟨a, ?_⟩
  rw [hBe, hb0, hp0, ← had]
  ext i j; fin_cases i <;> fin_cases j <;> simp


-- created on 2026-10-20
