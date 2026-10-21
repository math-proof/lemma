import Mathlib
import sympy.Basic


/--
[roth_finite_rat_of_abs_le_of_den_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (B : ℝ) (N : ℕ) :
-- imply
  {q : ℚ | |(q : ℝ)| ≤ B ∧ q.den ≤ N}.Finite := by
-- proof
  let K : ℤ := ⌈B * N⌉
  let f : ℚ → ℤ × ℕ := fun q ↦ (q.num, q.den)
  refine Set.Finite.of_finite_image (f := f) ?_ ?_
  ·
    apply ((Set.finite_Icc (-K) K).prod (Set.finite_Icc 0 N)).subset
    rintro _ ⟨q, hq, rfl⟩
    have hden0 : (0 : ℝ) ≤ q.den := by positivity
    have hB : 0 ≤ B := (abs_nonneg (q : ℝ)).trans hq.1
    have hnum : |(q.num : ℝ)| ≤ B * N := calc
      _ = |(q : ℝ)| * q.den := by
        rw [Rat.cast_def, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q.den)]
        field_simp
      _ ≤ B * N := mul_le_mul hq.1 (by exact_mod_cast hq.2) hden0 hB
    have hnumKReal : |(q.num : ℝ)| ≤ (K : ℝ) :=
      hnum.trans (Int.le_ceil (B * N))
    have hnumK : |q.num| ≤ K := by exact_mod_cast hnumKReal
    change (-K ≤ q.num ∧ q.num ≤ K) ∧ 0 ≤ q.den ∧ q.den ≤ N
    refine ⟨abs_le.mp hnumK, Nat.zero_le _, hq.2⟩
  ·
    intro a _ b _ hab
    change (a.num, a.den) = (b.num, b.den) at hab
    apply Rat.ext
    · apply congrArg Prod.fst hab
    · apply congrArg Prod.snd hab


-- created on 2026-10-21
