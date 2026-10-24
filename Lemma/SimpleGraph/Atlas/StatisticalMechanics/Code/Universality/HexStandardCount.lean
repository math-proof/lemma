import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexStandardCount
open StatMech StatMech.Universality


/--
[hexRootedVertices_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStandardCount.lean)
-/
@[path]
private lemma hexRootedVertices_head_eq
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  (hexRootedVertices h ts).headI = 0 := by
-- proof
  apply StatMech.Universality.hexRootedVertices_head h ts

/--
[verticesAux_headI](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStandardCount.lean)
-/
@[path]
private lemma verticesAux_headI_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  (verticesAux m h ts).headI = m + halfStep h := by
-- proof
  apply StatMech.Universality.verticesAux_headI m h ts

/--
[verticesAux_injective_of_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStandardCount.lean)
-/
@[path]
private lemma verticesAux_injective_of_legal_eq :
-- imply
  ∀ (s : List ℤ) (m : ℂ) (h : ℤ), (∀ u ∈ s, u = 1 ∨ u = -1) → ∀ t : List ℤ, (∀ u ∈ t, u = 1 ∨ u = -1) → verticesAux m h s = verticesAux m h t → s = t := by
-- proof
  apply StatMech.Universality.verticesAux_injective_of_legal

/--
[hexRootedOrientation_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStandardCount.lean)
-/
@[path]
private lemma hexRootedOrientation_card_eq
  {n : ℕ}
-- given
  (h : ℤ) :
-- imply
  (hexRootedOrientationFinset h n).card = hlc_sawCount (-halfStep h) h n := by
-- proof
  apply StatMech.Universality.hexRootedOrientation_card h n

/--
[hexRootedOrientation_card_eq_literal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStandardCount.lean)
-/
@[path]
private lemma hexRootedOrientation_card_eq_literal_eq
  {n : ℕ}
-- given
  (h : ℤ) :
-- imply
  (hexRootedOrientationFinset h n).card = hlc_sawCount 0 0 n := by
-- proof
  apply StatMech.Universality.hexRootedOrientation_card_eq_literal h n

/--
[hlc_sawCount_le_standard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStandardCount.lean)
-/
@[path]
private lemma hlc_sawCount_le_standard_eq
  {n : ℕ} :
-- imply
  hlc_sawCount 0 0 n ≤ hexStandardSAWCountNat n := by
-- proof
  apply StatMech.Universality.hlc_sawCount_le_standard n

/--
[hexStandardSAWCountNat_le_three_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStandardCount.lean)
-/
@[path]
private lemma hexStandardSAWCountNat_le_three_mul_eq
  {n : ℕ} :
-- imply
  hexStandardSAWCountNat n ≤ 3 * hlc_sawCount 0 0 n := by
-- proof
  apply StatMech.Universality.hexStandardSAWCountNat_le_three_mul n

/--
[hexLiteralSAWCount_le_standard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStandardCount.lean)
-/
@[path]
private lemma hexLiteralSAWCount_le_standard_eq
  {n : ℕ} :
-- imply
  hexLiteralSAWCount n ≤ hexStandardSAWCount n := by
-- proof
  apply StatMech.Universality.hexLiteralSAWCount_le_standard n

/--
[hexStandardSAWCount_le_three_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStandardCount.lean)
-/
@[path]
private lemma hexStandardSAWCount_le_three_mul_eq
  {n : ℕ} :
-- imply
  hexStandardSAWCount n ≤ 3 * hexLiteralSAWCount n := by
-- proof
  apply StatMech.Universality.hexStandardSAWCount_le_three_mul n

/--
[hexStandardSAWCount_one_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStandardCount.lean)
-/
@[path]
private lemma hexStandardSAWCount_one_le_eq
  {n : ℕ} :
-- imply
  1 ≤ hexStandardSAWCount n := by
-- proof
  apply StatMech.Universality.hexStandardSAWCount_one_le n

/--
[hexStandard_connective_of_literal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStandardCount.lean)
-/
@[path]
private lemma hexStandard_connective_of_literal_eq
  {mu : ℝ}
-- given
  (hmu : Tendsto (fun n => (hexLiteralSAWCount n) ^ ((n : ℝ)⁻¹)) atTop (nhds mu)) :
-- imply
  Tendsto (fun n => (hexStandardSAWCount n) ^ ((n : ℝ)⁻¹)) atTop (nhds mu) := by
-- proof
  apply StatMech.Universality.hexStandard_connective_of_literal hmu

/--
[hexStandard_connective_constant_of_series](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStandardCount.lean)
-/
@[path]
private lemma hexStandard_connective_constant_of_series_eq
-- given
  (hdiv : ¬ Summable (fun n => hexLiteralSAWCount n * hexChiE ^ n))
  (hconv : ∀ x, 0 ≤ x → x < hexChiE → Summable (fun n => hexLiteralSAWCount n * x ^ n)) :
-- imply
  ∃ kappa : ℝ, 0 < kappa ∧ Tendsto (fun n => (hexStandardSAWCount n) ^ ((n : ℝ)⁻¹)) atTop (nhds kappa) ∧ kappa = Real.sqrt (2 + Real.sqrt 2) := by
-- proof
  apply StatMech.Universality.hexStandard_connective_constant_of_series hdiv hconv


-- created on 2026-10-23
