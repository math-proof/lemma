import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DiophantineApproximation.BakerDavenportAbsolute
open MetaMathlibExt


/--
[bakerDavenport_reduction_absolute_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DiophantineApproximation/BakerDavenportAbsolute.lean)
-/
@[path]
private lemma bakerDavenport_reduction_absolute_general_eq
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
  apply MetaMathlibExt.bakerDavenport_reduction_absolute_general M q hq kappa A mu B epsilon hA hB hepsilon hepsilonpos

/--
[bakerDavenport_reduction_absolute](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DiophantineApproximation/BakerDavenportAbsolute.lean)
-/
@[path]
private lemma bakerDavenport_reduction_absolute_eq
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
  apply MetaMathlibExt.bakerDavenport_reduction_absolute M hM kappa hkappa j q hq hqM A mu B epsilon hA hB hepsilon hepsilonpos


-- created on 2026-10-20
