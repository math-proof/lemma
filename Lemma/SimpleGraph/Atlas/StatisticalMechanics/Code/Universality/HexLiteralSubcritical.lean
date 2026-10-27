import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralSubcritical.Part4
open StatMech StatMech.Universality


/--
[hls_exact_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hls_exact_length_eq
  {a : ℂ}
  {n : ℕ}
  {d : hls_ExactSAW a h0 n}
-- given
  (h0 : ℤ) :
-- imply
  d.1.length = n := by
-- proof
  apply StatMech.Universality.hls_exact_length a h0 n d

/--
[hls_encode_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hls_encode_injective_eq
  {a : ℂ}
  {n : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  Function.Injective (hls_encode a h0 n) := by
-- proof
  apply StatMech.Universality.hls_encode_injective a h0 n

/--
[hlc_sawCount_le_two_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hlc_sawCount_le_two_pow_eq
  {a : ℂ}
  {n : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  hlc_sawCount a h0 n ≤ 2 ^ n := by
-- proof
  apply StatMech.Universality.hlc_sawCount_le_two_pow a h0 n

/--
[hlc_sawCountR_le_two_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hlc_sawCountR_le_two_pow_eq
  {a : ℂ}
  {n : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  hlc_sawCountR a h0 n ≤ (2 : ℝ) ^ n := by
-- proof
  apply StatMech.Universality.hlc_sawCountR_le_two_pow a h0 n

/--
[hls_encode_ne_allTrue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hls_encode_ne_allTrue_eq
  {a : ℂ}
  {d : hls_ExactSAW a h0 6}
-- given
  (h0 : ℤ) :
-- imply
  hls_encode a h0 6 d ≠ hls_allTrue := by
-- proof
  apply StatMech.Universality.hls_encode_ne_allTrue a h0 d

/--
[hls_encode_ne_allFalse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hls_encode_ne_allFalse_eq
  {a : ℂ}
  {d : hls_ExactSAW a h0 6}
-- given
  (h0 : ℤ) :
-- imply
  hls_encode a h0 6 d ≠ hls_allFalse := by
-- proof
  apply StatMech.Universality.hls_encode_ne_allFalse a h0 d

/--
[hls_card_encodedSix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hls_card_encodedSix_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (hls_encodedSix a h0).card = hlc_sawCount a h0 6 := by
-- proof
  apply StatMech.Universality.hls_card_encodedSix a h0

/--
[hlc_sawCount_six_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hlc_sawCount_six_le_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hlc_sawCount a h0 6 ≤ 62 := by
-- proof
  apply StatMech.Universality.hlc_sawCount_six_le a h0

/--
[hlc_sawCount_six_blocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hlc_sawCount_six_blocks_eq
  {a : ℂ}
  {q r : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  hlc_sawCount a h0 (6 * q + r) ≤ 62 ^ q * 2 ^ r := by
-- proof
  apply StatMech.Universality.hlc_sawCount_six_blocks a h0 q r

/--
[hlc_sawCountR_six_block_term_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hlc_sawCountR_six_block_term_bound_eq
  {a : ℂ}
  {x : ℝ}
  {q r : ℕ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  hlc_sawCountR a h0 (6 * q + r) * x ^ (6 * q + r) ≤ ((2 : ℝ) * x) ^ r * ((62 : ℝ) * x ^ 6) ^ q := by
-- proof
  apply StatMech.Universality.hlc_sawCountR_six_block_term_bound a h0 x hx q r

/--
[hlc_sawCountR_summable_of_sixtyTwo_mul_pow_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hlc_sawCountR_summable_of_sixtyTwo_mul_pow_lt_one_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (hcontract : (62 : ℝ) * x ^ 6 < 1) :
-- imply
  Summable (fun n => hlc_sawCountR a h0 n * x ^ n) := by
-- proof
  apply StatMech.Universality.hlc_sawCountR_summable_of_sixtyTwo_mul_pow_lt_one a h0 x hx hcontract

/--
[hlc_sawCountR_summable_le_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hlc_sawCountR_summable_le_half_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (hle : x ≤ 1 / 2) :
-- imply
  Summable (fun n => hlc_sawCountR a h0 n * x ^ n) := by
-- proof
  apply StatMech.Universality.hlc_sawCountR_summable_le_half a h0 x hx hle

/--
[hlc_sawCountR_summable_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hlc_sawCountR_summable_half_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  Summable (fun n => hlc_sawCountR a h0 n * ((1 : ℝ) / 2) ^ n) := by
-- proof
  apply StatMech.Universality.hlc_sawCountR_summable_half a h0

/--
[hlc_sawCountR_summable_lt_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hlc_sawCountR_summable_lt_half_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (hlt : x < 1 / 2) :
-- imply
  Summable (fun n => hlc_sawCountR a h0 n * x ^ n) := by
-- proof
  apply StatMech.Universality.hlc_sawCountR_summable_lt_half a h0 x hx hlt

/--
[hzc_sawCount_summable_lt_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hzc_sawCount_summable_lt_half_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (hlt : x < 1 / 2) :
-- imply
  Summable (fun n => (hzc_sawCount a h0 n : ℝ) * x ^ n) := by
-- proof
  apply StatMech.Universality.hzc_sawCount_summable_lt_half a h0 x hx hlt

/--
[hls_half_lt_hexChiE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hls_half_lt_hexChiE_eq :
-- imply
  (1 : ℝ) / 2 < hexChiE := by
-- proof
  apply StatMech.Universality.hls_half_lt_hexChiE

/--
[hlc_sawCountR_subcritical_of_ge_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hlc_sawCountR_subcritical_of_ge_half_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (hsharp : ∀ x : ℝ, 1 / 2 ≤ x → x < hexChiE → Summable (fun n => hlc_sawCountR a h0 n * x ^ n)) :
-- imply
  ∀ x : ℝ, 0 ≤ x → x < hexChiE → Summable (fun n => hlc_sawCountR a h0 n * x ^ n) := by
-- proof
  apply StatMech.Universality.hlc_sawCountR_subcritical_of_ge_half a h0 hsharp

/--
[hlc_sawCountR_subcritical_of_noncontracting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean)
-/
@[path]
private lemma hlc_sawCountR_subcritical_of_noncontracting_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (hsharp : ∀ x : ℝ, 0 ≤ x → 1 ≤ (62 : ℝ) * x ^ 6 → x < hexChiE → Summable (fun n => hlc_sawCountR a h0 n * x ^ n)) :
-- imply
  ∀ x : ℝ, 0 ≤ x → x < hexChiE → Summable (fun n => hlc_sawCountR a h0 n * x ^ n) := by
-- proof
  apply StatMech.Universality.hlc_sawCountR_subcritical_of_noncontracting a h0 hsharp


-- created on 2026-10-23
