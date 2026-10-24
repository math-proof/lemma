import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[bakerDavenport_reduction_absolute_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DiophantineApproximation/BakerDavenportAbsolute.lean)
-/
@[path]
lemma bakerDavenport_reduction_absolute_general
  {M q : ℕ}
  {kappa A mu B epsilon : ℝ}
-- given
  (hq : 0 < q)
  (hA : 0 < A)
  (hB : 1 < B)
  (hepsilon : epsilon = |mu * (q : ℝ) - (round (mu * (q : ℝ)) : ℝ)| - (M : ℝ) * |kappa * (q : ℝ) - (round (kappa * (q : ℝ)) : ℝ)|)
  (hepsilonpos : 0 < epsilon) :
-- imply
  ¬∃ (r s w : ℕ), r ≤ M ∧
    (w : ℝ) ≥ Real.log (A * (q : ℝ) / epsilon) / Real.log B ∧
    |(r : ℝ) * kappa - (s : ℝ) + mu| < A * (B⁻¹) ^ w := by
-- proof
  rintro ⟨r, s, w, hle, hwlog, hlt⟩
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hAq : 0 < A * (q : ℝ) / epsilon := by positivity
  have h1 : Real.log (A * (q : ℝ) / epsilon) ≤ (w : ℝ) * Real.log B := by
    rwa [ge_iff_le, div_le_iff₀ hlogB] at hwlog
  have h2 : Real.log (A * (q : ℝ) / epsilon) ≤ Real.log (B ^ w) := by
    rwa [Real.log_pow]
  have hBpos : (0 : ℝ) < B := by linarith
  have hBwpos : (0 : ℝ) < B ^ w := pow_pos hBpos w
  have hBw : A * (q : ℝ) / epsilon ≤ B ^ w :=
    (Real.log_le_log_iff hAq hBwpos).mp h2
  have hexp : A * (B⁻¹) ^ w ≤ epsilon / (q : ℝ) := by
    rw [inv_pow, le_div_iff₀ hqR]
    have h3 : A * (q : ℝ) ≤ (B ^ w) * epsilon := by
      rw [div_le_iff₀ hepsilonpos] at hBw
      linarith
    have hBwne : (B ^ w) ≠ 0 := ne_of_gt hBwpos
    have h5 : A * (B ^ w)⁻¹ * (q : ℝ) = (A * (q : ℝ)) * (B ^ w)⁻¹ := by ring
    have h6 : (A * (q : ℝ)) * (B ^ w)⁻¹ ≤ ((B ^ w) * epsilon) * (B ^ w)⁻¹ :=
      mul_le_mul_of_nonneg_right h3 (le_of_lt (inv_pos.mpr hBwpos))
    have h7 : ((B ^ w) * epsilon) * (B ^ w)⁻¹ = epsilon := by
      field_simp
    linarith
  have hLamlt : |(r : ℝ) * kappa - (s : ℝ) + mu| < epsilon / (q : ℝ) :=
    lt_of_lt_of_le hlt hexp
  have hcore := nearestInteger_reduction_core q M r kappa mu s hle epsilon hepsilon
  push_cast at hcore
  rw [lt_div_iff₀ hqR] at hLamlt
  linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bakerDavenport_reduction_absolute](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DiophantineApproximation/BakerDavenportAbsolute.lean)
-/
@[path]
lemma bakerDavenport_reduction_absolute
  {M : ℕ}
  {kappa : ℝ}
  {j q : ℕ}
  {A mu B epsilon : ℝ}
-- given
  (hM : 0 < M)
  (hkappa : Irrational kappa)
  (hq : q = (kappa.convergent j).den)
  (hqM : 6 * M < q)
  (hA : 0 < A)
  (hB : 1 < B)
  (hepsilon : epsilon = |mu * (q : ℝ) - (round (mu * (q : ℝ)) : ℝ)| - (M : ℝ) * |kappa * (q : ℝ) - (round (kappa * (q : ℝ)) : ℝ)|)
  (hepsilonpos : 0 < epsilon) :
-- imply
  ¬∃ (r s w : ℕ), 0 < r ∧ 0 < s ∧ 0 < w ∧ r ≤ M ∧
    (w : ℝ) ≥ Real.log (A * (q : ℝ) / epsilon) / Real.log B ∧
    0 < |(r : ℝ) * kappa - (s : ℝ) + mu| ∧
    |(r : ℝ) * kappa - (s : ℝ) + mu| < A * (B⁻¹) ^ w := by
-- proof
  rintro ⟨r, s, w, -, -, -, hle, hwlog, -, hlt⟩
  exact bakerDavenport_reduction_absolute_general M q (by omega) kappa A mu B epsilon hA hB
    hepsilon hepsilonpos ⟨r, s, w, hle, hwlog, hlt⟩

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
