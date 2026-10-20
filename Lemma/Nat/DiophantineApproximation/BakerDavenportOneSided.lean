import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DiophantineApproximation.BakerDavenportOneSided
open MetaMathlibExt


/--
[bakerDavenport_reduction_oneSided_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DiophantineApproximation/BakerDavenportOneSided.lean)
-/
@[path]
private lemma bakerDavenport_reduction_oneSided_general_eq
  {N q : ℕ}
  {γ A μ B ξ : ℝ}
-- given
  (hq : 0 < q)
  (hA : 0 < A)
  (hB : 1 < B)
  (hξ : ξ = |μ * (q : ℝ) - (round (μ * (q : ℝ)) : ℝ)| - (N : ℝ) * |γ * (q : ℝ) - (round (γ * (q : ℝ)) : ℝ)|)
  (hξpos : 0 < ξ) :
-- imply
  ¬∃ (u v w : ℕ), u ≤ N ∧
    (w : ℝ) ≥ Real.log (A * (q : ℝ) / ξ) / Real.log B ∧
    0 < (u : ℝ) * γ - (v : ℝ) + μ ∧
    (u : ℝ) * γ - (v : ℝ) + μ < A * (B⁻¹) ^ w := by
-- proof
  apply MetaMathlibExt.bakerDavenport_reduction_oneSided_general N q hq γ A μ B ξ hA hB hξ hξpos

/--
[bakerDavenport_reduction_oneSided](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DiophantineApproximation/BakerDavenportOneSided.lean)
-/
@[path]
private lemma bakerDavenport_reduction_oneSided_eq
  {N : ℕ}
  {γ : ℝ}
  {j q : ℕ}
  {A μ B ξ : ℝ}
-- given
  (hN : 0 < N)
  (hγ : Irrational γ)
  (hq : q = (γ.convergent j).den)
  (hqN : 6 * N < q)
  (hA : 0 < A)
  (hB : 1 < B)
  (hξ : ξ = |μ * (q : ℝ) - (round (μ * (q : ℝ)) : ℝ)| - (N : ℝ) * |γ * (q : ℝ) - (round (γ * (q : ℝ)) : ℝ)|)
  (hξpos : 0 < ξ) :
-- imply
  ¬∃ (u v w : ℕ), 0 < u ∧ 0 < v ∧ 0 < w ∧ u ≤ N ∧
    (w : ℝ) ≥ Real.log (A * (q : ℝ) / ξ) / Real.log B ∧
    0 < (u : ℝ) * γ - (v : ℝ) + μ ∧
    (u : ℝ) * γ - (v : ℝ) + μ < A * (B⁻¹) ^ w := by
-- proof
  apply MetaMathlibExt.bakerDavenport_reduction_oneSided N hN γ hγ j q hq hqN A μ B ξ hA hB hξ hξpos


-- created on 2026-10-20
