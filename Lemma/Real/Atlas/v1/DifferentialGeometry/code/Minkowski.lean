import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialGeometry.code.Minkowski
open Finset Minkowski


namespace Minkowski

/--
[minkowskiInner_smul_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Minkowski.lean)
-/
@[path]
lemma minkowskiInner_smul_self
  {n : ℕ}
  {n : ℕ}
  {c : ℝ}
  {v : Fin (n + 1) → ℝ} :
-- imply
  minkowskiInner n (c • v) (c • v) = c ^ 2 * minkowskiInner n v v := by
-- proof
  simp only [minkowskiInner, Pi.smul_apply, smul_eq_mul]
  have h₁ : ∑ x : Fin n, c * v (Fin.castSucc x) * (c * v (Fin.castSucc x)) =
    c ^ 2 * ∑ x : Fin n, v (Fin.castSucc x) * v (Fin.castSucc x) := by
    conv_lhs => arg 2; ext x; rw [show c * v (Fin.castSucc x) * (c * v (Fin.castSucc x)) =
      c ^ 2 * (v (Fin.castSucc x) * v (Fin.castSucc x)) from by ring]
    rw [← Finset.mul_sum]
  linarith

end Minkowski

namespace Minkowski

/--
[minkowskiInner_smul_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Minkowski.lean)
-/
@[path]
lemma minkowskiInner_smul_left
  {n : ℕ}
  {n : ℕ}
  {c : ℝ}
  {v w : Fin (n + 1) → ℝ} :
-- imply
  minkowskiInner n (c • v) w = c * minkowskiInner n v w := by
-- proof
  simp only [minkowskiInner, Pi.smul_apply, smul_eq_mul]
  have h₁ : ∑ x : Fin n, c * v (Fin.castSucc x) * w (Fin.castSucc x) =
    c * ∑ x : Fin n, v (Fin.castSucc x) * w (Fin.castSucc x) := by
      conv_lhs => arg 2; ext x; rw [show c * v (Fin.castSucc x) * w (Fin.castSucc x) =
        c * (v (Fin.castSucc x) * w (Fin.castSucc x)) from by ring]
      rw [← Finset.mul_sum]
  linarith

end Minkowski

namespace Minkowski

/--
[minkowski_orthogonal_complement_positive_definite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Minkowski.lean)
-/
@[path]
lemma minkowski_orthogonal_complement_positive_definite
  {n : ℕ}
  {n : ℕ}
  {X : Fin (n + 1) → ℝ}
-- given
  (hX : minkowskiInner n X X < 0) :
-- imply
  ∀ Y : Fin (n + 1) → ℝ, Y ≠ 0 → minkowskiInner n X Y = 0 → minkowskiInner n Y Y > 0 := by
-- proof
  intro Y hY horth
  simp only [minkowskiInner] at hX horth ⊢
  set Xn := X (Fin.last n)
  set Yn := Y (Fin.last n)
  set sXX := ∑ i : Fin n, X (Fin.castSucc i) * X (Fin.castSucc i)
  set sYY := ∑ i : Fin n, Y (Fin.castSucc i) * Y (Fin.castSucc i)
  set sXY := ∑ i : Fin n, X (Fin.castSucc i) * Y (Fin.castSucc i)
  have hXn_sq : sXX < Xn * Xn := by linarith
  have hXn_ne : Xn ≠ 0 := by
    intro h
    have h1 : sXX < 0 := by linarith [show Xn * Xn = 0 from by rw [h]; ring]
    have h2 : (0 : ℝ) ≤ sXX := Finset.sum_nonneg fun i _ =>
      mul_self_nonneg (a := X (Fin.castSucc i))
    linarith
  have horth' : sXY = Xn * Yn := by linarith
  have hsYY_pos : 0 < sYY := by
    by_contra h
    push Not at h
    have hsYY_nn : (0 : ℝ) ≤ sYY := Finset.sum_nonneg fun i _ =>
      mul_self_nonneg (a := Y (Fin.castSucc i))
    have hsYY_zero : sYY = 0 := le_antisymm h hsYY_nn
    have hYi_zero : ∀ i : Fin n, Y (Fin.castSucc i) = 0 := by
      intro i
      have h1 : (0 : ℝ) ≤ Y (Fin.castSucc i) * Y (Fin.castSucc i) :=
        mul_self_nonneg (a := Y (Fin.castSucc i))
      have h2 : Y (Fin.castSucc i) * Y (Fin.castSucc i) ≤ sYY :=
        Finset.single_le_sum (fun j _ => mul_self_nonneg (a := Y (Fin.castSucc j)))
          (Finset.mem_univ i)
      have h3 : Y (Fin.castSucc i) * Y (Fin.castSucc i) = 0 := by linarith
      exact mul_self_eq_zero.mp h3
    have hsXY_zero : sXY = 0 := by
      simp only [sXY]
      apply Finset.sum_eq_zero
      intro i _
      rw [hYi_zero i, mul_zero]
    rw [hsXY_zero] at horth'
    have hYn_zero : Yn = 0 := by
      obtain h | h := mul_eq_zero.mp horth'.symm
      · exact absurd h hXn_ne
      · exact h
    have hY_zero : Y = 0 := by
      ext j
      simp only [Pi.zero_apply]
      by_cases hj : j = Fin.last n
      · rw [hj]; exact hYn_zero
      · have : ∃ i : Fin n, Fin.castSucc i = j := by
        have hlt : j.val < n := by
          obtain ⟨val, hval⟩ := j
          simp only [Fin.last, Fin.ext_iff] at hj
          exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hval) hj
        exact ⟨⟨j.val, hlt⟩, by simp [Fin.castSucc]⟩
        obtain ⟨i, rfl⟩ := this
        exact hYi_zero i
    exact absurd hY_zero hY
  have hCS : sXY ^ 2 ≤ sXX * sYY := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => X (Fin.castSucc i)) (fun i => Y (Fin.castSucc i))
    simp only [sq] at this ⊢
    exact this
  have hXn_sq_pos : (0 : ℝ) < Xn * Xn := by
    obtain h | h := ne_iff_lt_or_gt.mp hXn_ne
    · exact mul_pos_of_neg_of_neg h h
    · exact mul_pos h h
  have hYn_sq : Yn * Yn * (Xn * Xn) = sXY * sXY := by
    rw [horth']; ring
  have hCS' : sXY * sXY ≤ sXX * sYY := by
    have := hCS; rw [sq] at this; exact this
  nlinarith

end Minkowski


-- created on 2026-10-23
