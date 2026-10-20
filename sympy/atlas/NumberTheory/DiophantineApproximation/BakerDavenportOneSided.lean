/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DiophantineApproximation/BakerDavenportOneSided.lean -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.DiophantineApproximation.Basic

namespace MetaMathlibExt

/-- One-sided Baker–Davenport reduction with only the hypotheses the argument uses: if
`ξ = ‖μq‖ - N‖γq‖` is positive, no `u ≤ N` and `w ≥ log (Aq/ξ) / log B` satisfy
`0 < uγ - v + μ < A B⁻ʷ`. `bakerDavenport_reduction_oneSided` is the source-shaped form. -/
theorem bakerDavenport_reduction_oneSided_general
    (N q : ℕ) (hq : 0 < q)
    (γ A μ B ξ : ℝ)
    (hA : 0 < A) (hB : 1 < B)
    (hξ : ξ = |μ * (q : ℝ) - (round (μ * (q : ℝ)) : ℝ)| -
      (N : ℝ) * |γ * (q : ℝ) - (round (γ * (q : ℝ)) : ℝ)|)
    (hξpos : 0 < ξ) :
    ¬∃ (u v w : ℕ), u ≤ N ∧
      (w : ℝ) ≥ Real.log (A * (q : ℝ) / ξ) / Real.log B ∧
      0 < (u : ℝ) * γ - (v : ℝ) + μ ∧
      (u : ℝ) * γ - (v : ℝ) + μ < A * (B⁻¹) ^ w := by
  rintro ⟨u, v, w, huN, hw, hΛpos, hΛlt⟩
  -- Basic positivity facts.
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hAqξ : 0 < A * (q : ℝ) / ξ := by positivity
  have hBw : (0 : ℝ) < B ^ w := by positivity
  -- From the lower bound on w, deduce `A * (B⁻¹)^w ≤ ξ / q`.
  have hlogle : Real.log (A * (q : ℝ) / ξ) ≤ (w : ℝ) * Real.log B := by
    have h := (div_le_iff₀ hlogB).mp hw
    linarith
  have hlogle2 : Real.log (A * (q : ℝ) / ξ) ≤ Real.log (B ^ w) := by
    rw [Real.log_pow]
    exact hlogle
  have hle3 : A * (q : ℝ) / ξ ≤ B ^ w :=
    (Real.log_le_log_iff hAqξ hBw).mp hlogle2
  have hAq : A * (q : ℝ) ≤ B ^ w * ξ := by
    rwa [div_le_iff₀ hξpos] at hle3
  have hbound : A * (B⁻¹) ^ w ≤ ξ / (q : ℝ) := by
    rw [inv_pow, ← div_eq_mul_inv]
    rw [div_le_div_iff₀ hBw hqpos]
    linarith [mul_comm (B ^ w) ξ]
  -- Hence with `Λ = uγ - v + μ`, `0 < q * Λ < ξ`.
  set Λ : ℝ := (u : ℝ) * γ - (v : ℝ) + μ with hΛdef
  have hΛlt2 : Λ < ξ / (q : ℝ) := lt_of_lt_of_le hΛlt hbound
  have hqΛpos : 0 < (q : ℝ) * Λ := mul_pos hqpos hΛpos
  have hqΛlt : (q : ℝ) * Λ < ξ := by
    have h : Λ * (q : ℝ) < ξ := (lt_div_iff₀ hqpos).mp hΛlt2
    rwa [mul_comm] at h
  -- The one-sided gap exceeds the `N`-scaled rounding error of `γq`.
  have hNδraw : (N : ℝ) * |γ * (q : ℝ) - (round (γ * (q : ℝ)) : ℝ)| <
      |μ * (q : ℝ) - (round (μ * (q : ℝ)) : ℝ)| := by linarith
  -- Distances to the nearest integer.
  set p : ℤ := round (γ * (q : ℝ)) with hpdef
  set r : ℤ := round (μ * (q : ℝ)) with hrdef
  set δ : ℝ := |γ * (q : ℝ) - (p : ℝ)| with hδdef
  set ε : ℝ := |μ * (q : ℝ) - (r : ℝ)| with hεdef
  have hεhalf : ε ≤ 1 / 2 := abs_sub_round _
  have hδnn : 0 ≤ δ := abs_nonneg _
  have hNδ : (N : ℝ) * δ < ε := hNδraw
  have huN' : (u : ℝ) ≤ (N : ℝ) := by exact_mod_cast huN
  have huδ : (u : ℝ) * δ ≤ (N : ℝ) * δ :=
    mul_le_mul_of_nonneg_right huN' hδnn
  -- The errors `e₁ = γq - p`, `e₂ = μq - r` and the integer `k = u*p + r - v*q`.
  set e₁ : ℝ := γ * (q : ℝ) - (p : ℝ) with he1def
  set e₂ : ℝ := μ * (q : ℝ) - (r : ℝ) with he2def
  have hδeq : δ = |e₁| := rfl
  have hεeq : ε = |e₂| := rfl
  set k : ℤ := (u : ℤ) * p + r - (v : ℤ) * (q : ℤ) with hkdef
  have hkey : (q : ℝ) * Λ = (u : ℝ) * e₁ + e₂ + (k : ℝ) := by
    simp only [hΛdef, he1def, he2def, hkdef]
    push_cast
    ring
  have hub : |(u : ℝ) * e₁| = (u : ℝ) * δ := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (u : ℝ)), ← hδeq]
  have hSbound : |(u : ℝ) * e₁ + e₂| ≤ (N : ℝ) * δ + ε := by
    have h1 : |(u : ℝ) * e₁ + e₂| ≤ |(u : ℝ) * e₁| + |e₂| := abs_add_le _ _
    rw [hub, ← hεeq] at h1
    linarith
  have hSlow : ε ≤ |(u : ℝ) * e₁ + e₂| + (u : ℝ) * δ := by
    have heq : ((u : ℝ) * e₁ + e₂) + (-((u : ℝ) * e₁)) = e₂ := by ring
    have htri : |e₂| ≤ |(u : ℝ) * e₁ + e₂| + |(u : ℝ) * e₁| := by
      have h := abs_add_le ((u : ℝ) * e₁ + e₂) (-((u : ℝ) * e₁))
      rwa [heq, abs_neg] at h
    rw [← hεeq, hub] at htri
    exact htri
  rcases lt_trichotomy (k : ℤ) 0 with hkneg | hkzero | hkpos
  · -- Case `k < 0`: then `(k : ℝ) ≤ -1`, so `q*Λ ≤ Nδ + ε - 1 < 0`.
    have hk1 : (k : ℝ) ≤ -1 := by
      have h : k + 1 ≤ 0 := by omega
      have h' : (k : ℝ) + 1 ≤ 0 := by exact_mod_cast h
      linarith
    have hSle : (u : ℝ) * e₁ + e₂ ≤ |(u : ℝ) * e₁ + e₂| := le_abs_self _
    linarith
  · -- Case `k = 0`: then `q*Λ = u*e₁ + e₂`, whose abs is at least `ε - uδ ≥ ξ`.
    have hk0 : (k : ℝ) = 0 := by exact_mod_cast hkzero
    have hqΛeq : (q : ℝ) * Λ = (u : ℝ) * e₁ + e₂ := by linarith
    have habs : |(u : ℝ) * e₁ + e₂| = (q : ℝ) * Λ := by
      rw [← hqΛeq]
      exact abs_of_pos hqΛpos
    linarith
  · -- Case `k > 0`: then `(k : ℝ) ≥ 1`, so `1 < 2ε ≤ 1`.
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      have h : 1 ≤ k := by omega
      exact_mod_cast h
    have hSge : -|(u : ℝ) * e₁ + e₂| ≤ (u : ℝ) * e₁ + e₂ := neg_abs_le _
    linarith

set_option linter.unusedVariables false in
/-- One-sided Baker–Davenport reduction lemma.

Concept `jis_rank27_baker_davenport_one_sided`, semantic id
`jis_grounded_3d649f47290c78b9a73677c9`.
Source: Bilizimbéyé Edjeou, Amadou Tall, and Mohamed Ben Fraj Ben Maaouia,
"Powers of Two as Sums of Three Lucas Numbers," Journal of Integer Sequences 23
(2020), Article 20.8.8, <https://cs.uwaterloo.ca/journals/JIS/VOL23/Edjeou/edj4.tex>,
exact source span: Lemma `lem1`, lines 200–211.
Source-file SHA-256
`ef293eb1fb3bec15a47898830b7ed2ea8c38ca4c491750d5a197cb16e00125fc`;
exact-span SHA-256
`e8df3e4bbefc3b0825b721bcff7f5d918b3006429e63ee4b1d902ffce1f606d7`.

Here `|x - round x|` formalizes distance to the nearest integer, and this
declaration is the one-sided form from the cited lemma: the final linear form
`(u : ℝ) * γ - (v : ℝ) + μ` appears with one-sided strict inequalities and no
absolute-value bars.
It follows from `bakerDavenport_reduction_oneSided_general`. The hypotheses `hN`, `hγ`
and `hq`, and the positivity conditions on `u`, `v` and `w`, are unused and keep the source's
shape; `hqN` only supplies `0 < q`.
Proves `Wanted` entry `bakerDavenport_reduction_oneSided`.
-/
theorem bakerDavenport_reduction_oneSided
    (N : ℕ) (hN : 0 < N)
    (γ : ℝ) (hγ : Irrational γ)
    (j : ℕ) (q : ℕ)
    (hq : q = (γ.convergent j).den)
    (hqN : 6 * N < q)
    (A μ B ξ : ℝ)
    (hA : 0 < A) (hB : 1 < B)
    (hξ : ξ = |μ * (q : ℝ) - (round (μ * (q : ℝ)) : ℝ)| -
      (N : ℝ) * |γ * (q : ℝ) - (round (γ * (q : ℝ)) : ℝ)|)
    (hξpos : 0 < ξ) :
    ¬∃ (u v w : ℕ), 0 < u ∧ 0 < v ∧ 0 < w ∧ u ≤ N ∧
      (w : ℝ) ≥ Real.log (A * (q : ℝ) / ξ) / Real.log B ∧
      0 < (u : ℝ) * γ - (v : ℝ) + μ ∧
      (u : ℝ) * γ - (v : ℝ) + μ < A * (B⁻¹) ^ w := by
  rintro ⟨u, v, w, -, -, -, huN, hw, hΛpos, hΛlt⟩
  exact bakerDavenport_reduction_oneSided_general N q (by omega) γ A μ B ξ hA hB hξ hξpos
    ⟨u, v, w, huN, hw, hΛpos, hΛlt⟩

end MetaMathlibExt
