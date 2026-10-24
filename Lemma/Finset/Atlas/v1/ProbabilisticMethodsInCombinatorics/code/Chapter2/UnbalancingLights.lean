import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter2.UnbalancingLights
open Finset BigOperators UnbalancingLights


namespace UnbalancingLights

/--
[boolToSign_isSign](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/UnbalancingLights.lean)
-/
@[path]
lemma boolToSign_isSign
  {b : Bool} :
-- imply
  boolToSign b = 1 ∨ boolToSign b = -1 := by
-- proof
  cases b <;> simp [boolToSign]

end UnbalancingLights

namespace UnbalancingLights

/--
[isSignVec_boolToSign](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/UnbalancingLights.lean)
-/
@[path]
lemma isSignVec_boolToSign
  {n : ℕ}
  {f : Fin n → Bool} :
-- imply
  IsSignVec (fun j => boolToSign (f j)) :=
-- proof
  fun _ => boolToSign_isSign _

end UnbalancingLights

namespace UnbalancingLights

/--
[exists_ge_sum_div](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/UnbalancingLights.lean)
-/
@[path]
lemma exists_ge_sum_div
  [Fintype ι]
  [Nonempty ι]
  {f : ι → ℤ} :
-- imply
  ∃ x : ι, (Fintype.card ι : ℤ) * f x ≥ ∑ y : ι, f y := by
-- proof
  by_contra h
  push Not at h
  have h1 := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    (fun x (_ : x ∈ Finset.univ) => h x)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  rw [← Finset.mul_sum] at h1
  exact lt_irrefl _ h1

end UnbalancingLights

namespace UnbalancingLights

/--
[bilinear_eq_row_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/UnbalancingLights.lean)
-/
@[path]
lemma bilinear_eq_row_sum
  {m n : ℕ}
  {a : Fin m → Fin n → ℤ}
  {x : Fin m → ℤ}
  {y : Fin n → ℤ} :
-- imply
  ∑ i : Fin m, ∑ j : Fin n, a i j * x i * y j = ∑ i : Fin m, (∑ j : Fin n, a i j * y j) * x i := by
-- proof
  congr 1; ext i; rw [Finset.sum_mul]; congr 1; ext j; ring

end UnbalancingLights

namespace UnbalancingLights

/--
[exists_sign_mul_eq_abs](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/UnbalancingLights.lean)
-/
@[path]
lemma exists_sign_mul_eq_abs
  {z : ℤ} :
-- imply
  ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ s * z = := by
-- proof
  by_cases h : 0 ≤ z
  · exact ⟨1, Or.inl rfl, by simp [abs_of_nonneg h]⟩
  · push Not at h
    exact ⟨-1, Or.inr rfl, by simp [abs_of_neg h]⟩

end UnbalancingLights

namespace UnbalancingLights

/--
[greedy_row_selection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/UnbalancingLights.lean)
-/
@[path]
lemma greedy_row_selection
  {m n : ℕ}
  {a : Fin m → Fin n → ℤ}
  {y : Fin n → ℤ} :
-- imply
  ∃ x : Fin m → ℤ, IsSignVec x ∧ ∑ i : Fin m, ∑ j : Fin n, a i j * x i * y j = ∑ i : Fin m, := by
-- proof
  choose x hx using fun i => exists_sign_mul_eq_abs (∑ j, a i j * y j)
  refine ⟨x, fun i => (hx i).1, ?_⟩
  rw [bilinear_eq_row_sum]
  congr 1; ext i; rw [mul_comm]; exact (hx i).2

end UnbalancingLights

namespace UnbalancingLights

/--
[sign_mul_boolToSign](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/UnbalancingLights.lean)
-/
@[path]
lemma sign_mul_boolToSign
  {a : ℤ}
  {b : Bool}
-- given
  (ha : a = 1 ∨ a = -1) :
-- imply
  a * boolToSign b = boolToSign (decide (a = -1) ^^ b) := by
-- proof
  obtain rfl | rfl := ha
  · simp [boolToSign]
  · simp [boolToSign]; cases b <;> simp

end UnbalancingLights

namespace UnbalancingLights

/--
[sum_abs_row_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/UnbalancingLights.lean)
-/
@[path]
lemma sum_abs_row_eq
  {n : ℕ}
  {a : Fin n → ℤ}
-- given
  (ha : ∀ j, a j = 1 ∨ a j = -1) :
-- imply
  ∑ y : Fin n → Bool, (|∑ j, a j * boolToSign (y j)| : ℤ) = ∑ y : Fin n → Bool, := by
-- proof
  have key : ∀ y : Fin n → Bool,
    |∑ j, a j * boolToSign (y j)| = |∑ j, boolToSign ((signFlipEquiv a) y j)| := by
    intro y; congr 1; congr 1; ext j
    rw [sign_mul_boolToSign (a j) (ha j)]
    simp [signFlipEquiv, signFlip, Function.Involutive.toPerm]
  simp_rw [key]
  exact Fintype.sum_equiv (signFlipEquiv a) _ _ (fun y => rfl)

end UnbalancingLights

namespace UnbalancingLights

/--
[total_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/UnbalancingLights.lean)
-/
@[path]
lemma total_sum_eq
  {n : ℕ}
  {a : Fin n → Fin n → ℤ}
-- given
  (ha : IsSignMatrix a) :
-- imply
  ∑ y : Fin n → Bool, ∑ i : Fin n, := by
-- proof
  rw [Finset.sum_comm]
  simp_rw [sum_abs_row_eq _ (fun j => ha _ j)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, rademacherAbsExpect,
    nsmul_eq_mul]

end UnbalancingLights

namespace UnbalancingLights

/--
[unbalancing_lights](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/UnbalancingLights.lean)
-/
@[path]
lemma unbalancing_lights
  {n : ℕ}
  {a : Fin n → Fin n → ℤ}
-- given
  (ha : IsSignMatrix a) :
-- imply
  ∃ x y : Fin n → ℤ, IsSignVec x ∧ IsSignVec y ∧ (Fintype.card (Fin n → Bool) : ℤ) * ∑ i : Fin n, ∑ j : Fin n, a i j * x i * y j ≥ (n : ℤ) * rademacherAbsExpect n := by
-- proof
  obtain ⟨y₀, hy₀⟩ := exists_ge_sum_div (fun y : Fin n → Bool =>
    ∑ i : Fin n, |∑ j : Fin n, a i j * boolToSign (y j)|)
  let y_vec : Fin n → ℤ := fun j => boolToSign (y₀ j)
  obtain ⟨x, hx_sign, hx_eq⟩ := greedy_row_selection a y_vec
  refine ⟨x, y_vec, hx_sign, isSignVec_boolToSign y₀, ?_⟩
  rw [hx_eq]
  calc (Fintype.card (Fin n → Bool) : ℤ) * ∑ i, |∑ j, a i j * y_vec j|
    = (Fintype.card (Fin n → Bool) : ℤ) *
      ∑ i, |∑ j, a i j * boolToSign (y₀ j)| := rfl
    _ ≥ ∑ y : Fin n → Bool, ∑ i, |∑ j, a i j * boolToSign (y j)| := hy₀
    _ = (n : ℤ) * rademacherAbsExpect n := total_sum_eq a ha

end UnbalancingLights

/--
[signFlip_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/UnbalancingLights.lean)
-/
@[path]
private lemma signFlip_involutive_eq
  {n : ℕ}
  {a : Fin n → ℤ} :
-- imply
  Function.Involutive (signFlip a) := by
-- proof
  apply UnbalancingLights.signFlip_involutive a


-- created on 2026-10-23
