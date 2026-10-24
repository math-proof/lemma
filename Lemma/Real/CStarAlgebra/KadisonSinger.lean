import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.CStarAlgebra.KadisonSinger
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open MathlibExt.Analysis.CStarAlgebra.KadisonSinger
open MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted


namespace MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted

/--
[ksExists_paving_rate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger.lean)
-/
@[path]
private lemma ksExists_paving_rate (ε : ℝ) (hε : 0 < ε) :
  ∃ r : ℕ, 0 < r ∧
    2 * (1 / Real.sqrt r + Real.sqrt (1 / 2 : ℝ)) ^ 2 - 1 ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (6 / ε))
  have hN1 : 1 < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hNe : 6 / ε < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos : 0 < (N : ℝ) := lt_trans (by norm_num) hN1
  have hNnat : 0 < N := by exact_mod_cast hNpos
  refine ⟨N * N, Nat.mul_pos hNnat hNnat, ?_⟩
  have hsqrt : Real.sqrt ((N * N : ℕ) : ℝ) = N := by
    rw [Nat.cast_mul, ← pow_two, Real.sqrt_sq (Nat.cast_nonneg N)]
  rw [hsqrt]
  let x : ℝ := 1 / N
  let y : ℝ := Real.sqrt (1 / 2 : ℝ)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    rw [div_le_iff₀ hNpos]
    nlinarith
  have hsix : 6 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hNe
  have hxe : x < ε / 6 := by
    dsimp [x]
    rw [div_lt_iff₀ hNpos]
    nlinarith
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy1 : y ≤ 1 := Real.sqrt_le_one.mpr (by norm_num)
  have hy2 : y ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hxx : x * x ≤ x := by nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  have hxy : x * y ≤ x := by nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hy1)]
  change 2 * (x + y) ^ 2 - 1 ≤ ε
  nlinarith

end MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted

/--
[ksKadisonSingerPaving_of_finiteMSS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger.lean)
-/
@[path]
private lemma ksKadisonSingerPaving_of_finiteMSS
  (hMSS : FiniteMSSBound.{0}) (ε : ℝ) (hε : 0 < ε) :
  ∃ (r : ℕ), 0 < r ∧
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
      A.IsHermitian → (∀ i : Fin n, A i i = 0) → ‖A‖ ≤ 1 →
      ∃ (c : Fin n → Fin r), ∀ (j : Fin r),
        ‖pavingProj n r c j * A * pavingProj n r c j‖ ≤ ε := by
  obtain ⟨q, hq, hqε⟩ := ksExists_paving_rate ε hε
  refine ⟨q * q, Nat.mul_pos hq hq, ?_⟩
  intro n A hA hdiag hnorm
  obtain ⟨c, hc⟩ := andersonPaving_of_finiteMSS hMSS hq A hA hdiag hnorm
  refine ⟨c, ?_⟩
  intro j
  apply le_trans ?_ hqε
  simpa only [pavingProj] using hc j

end MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted

/--
[kadison_singer_paving](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger.lean)
-/
@[path]
lemma kadison_singer_paving
  {ε : ℝ}
-- given
  (hε : 0 < ε) :
-- imply
  ∃ (r : ℕ), 0 < r ∧
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
    A.IsHermitian → (∀ i : Fin n, A i i = 0) → ‖A‖ ≤ 1 →
    ∃ (c : Fin n → Fin r), ∀ (j : Fin r),
    ‖pavingProj n r c j * A * pavingProj n r c j‖ ≤ ε := by
-- proof
  exact ksKadisonSingerPaving_of_finiteMSS finiteMSSBound.{0} ε hε

end MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted


-- created on 2026-10-20
-- updated on 2026-10-23
