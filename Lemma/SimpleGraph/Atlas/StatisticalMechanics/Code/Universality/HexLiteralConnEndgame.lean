import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralConnEndgame
open StatMech StatMech.Universality


/--
[hexLiteralSAWCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralConnEndgame.lean)
-/
@[path]
private lemma hexLiteralSAWCount_eq_eq
  {a : ℂ}
  {n : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  hexLiteralSAWCount n = hlc_sawCountR a h0 n := by
-- proof
  apply StatMech.Universality.hexLiteralSAWCount_eq a h0 n

/--
[hexLiteralSAWCount_one_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralConnEndgame.lean)
-/
@[path]
private lemma hexLiteralSAWCount_one_le_eq
  {n : ℕ} :
-- imply
  1 ≤ hexLiteralSAWCount n := by
-- proof
  apply StatMech.Universality.hexLiteralSAWCount_one_le n

/--
[hexLiteralSAWCount_submultiplicative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralConnEndgame.lean)
-/
@[path]
private lemma hexLiteralSAWCount_submultiplicative_eq :
-- imply
  Submultiplicative hexLiteralSAWCount := by
-- proof
  apply StatMech.Universality.hexLiteralSAWCount_submultiplicative

/--
[hexLiteral_connective_constant_of_series](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralConnEndgame.lean)
-/
@[path]
private lemma hexLiteral_connective_constant_of_series_eq
-- given
  (hdiv : ¬ Summable (fun n => hexLiteralSAWCount n * hexChiE ^ n))
  (hconv : ∀ x, 0 ≤ x → x < hexChiE → Summable (fun n => hexLiteralSAWCount n * x ^ n)) :
-- imply
  ∃ kappa : ℝ, 0 < kappa ∧ Tendsto (fun n => (hexLiteralSAWCount n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧ kappa = Real.sqrt (2 + Real.sqrt 2) := by
-- proof
  apply StatMech.Universality.hexLiteral_connective_constant_of_series hdiv hconv

/--
[hlc_connective_constant_of_series](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralConnEndgame.lean)
-/
@[path]
private lemma hlc_connective_constant_of_series_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (hdiv : ¬ Summable (fun n => hlc_sawCountR a h0 n * hexChiE ^ n))
  (hconv : ∀ x, 0 ≤ x → x < hexChiE → Summable (fun n => hlc_sawCountR a h0 n * x ^ n)) :
-- imply
  ∃ kappa : ℝ, 0 < kappa ∧ Tendsto (fun n => (hlc_sawCountR a h0 n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧ kappa = Real.sqrt (2 + Real.sqrt 2) := by
-- proof
  apply StatMech.Universality.hlc_connective_constant_of_series a h0 hdiv hconv


-- created on 2026-10-23
