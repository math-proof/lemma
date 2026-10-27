import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[nearestInteger_reduction_core](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DiophantineApproximation/BakerDavenportNearestIntegerCore.lean)
-/
@[path]
lemma nearestInteger_reduction_core
  {q M u : ℕ}
  {kappa mu : ℝ}
  {v : ℤ}
  {epsilon : ℝ}
-- given
  (hu : u ≤ M)
  (heq : epsilon = |mu * (q : ℝ) - (round (mu * (q : ℝ)) : ℝ)| - (M : ℝ) * |kappa * (q : ℝ) - (round (kappa * (q : ℝ)) : ℝ)|) :
-- imply
  epsilon ≤ (q : ℝ) * |(u : ℝ) * kappa - (v : ℝ) + mu| := by
-- proof
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have huM : (u : ℝ) ≤ (M : ℝ) := by exact_mod_cast hu
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := by positivity
  have hmin := round_le (mu * (q : ℝ)) ((q : ℤ) * v - (u : ℤ) * round (kappa * (q : ℝ)))
  push_cast at hmin
  have hfactor : mu * (q : ℝ) + (u : ℝ) * (kappa * (q : ℝ)) - (q : ℝ) * (v : ℝ)
    = (q : ℝ) * ((u : ℝ) * kappa - (v : ℝ) + mu) := by ring
  have hsplit : mu * (q : ℝ) - ((q : ℝ) * (v : ℝ) - (u : ℝ) * (round (kappa * (q : ℝ)) : ℝ))
    = (mu * (q : ℝ) + (u : ℝ) * (kappa * (q : ℝ)) - (q : ℝ) * (v : ℝ))
      - (u : ℝ) * (kappa * (q : ℝ) - (round (kappa * (q : ℝ)) : ℝ)) := by ring
  have hub : |(u : ℝ) * (kappa * (q : ℝ) - (round (kappa * (q : ℝ)) : ℝ))|
    = (u : ℝ) * |kappa * (q : ℝ) - (round (kappa * (q : ℝ)) : ℝ)| := by
    rw [abs_mul, abs_of_nonneg hu0]
  have hqabs : |mu * (q : ℝ) + (u : ℝ) * (kappa * (q : ℝ)) - (q : ℝ) * (v : ℝ)|
    = (q : ℝ) * |(u : ℝ) * kappa - (v : ℝ) + mu| := by
    rw [hfactor, abs_mul, abs_of_nonneg hq0]
  have hle : (u : ℝ) * |kappa * (q : ℝ) - (round (kappa * (q : ℝ)) : ℝ)|
    ≤ (M : ℝ) * |kappa * (q : ℝ) - (round (kappa * (q : ℝ)) : ℝ)| :=
    mul_le_mul_of_nonneg_right huM (abs_nonneg _)
  have htri : |mu * (q : ℝ) - ((q : ℝ) * (v : ℝ) - (u : ℝ) * (round (kappa * (q : ℝ)) : ℝ))|
    ≤ |mu * (q : ℝ) + (u : ℝ) * (kappa * (q : ℝ)) - (q : ℝ) * (v : ℝ)|
      + (u : ℝ) * |kappa * (q : ℝ) - (round (kappa * (q : ℝ)) : ℝ)| := by
    rw [hsplit, ← hub]
    exact abs_sub _ _
  rw [hqabs] at htri
  linarith [heq, hmin, htri, hle]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
