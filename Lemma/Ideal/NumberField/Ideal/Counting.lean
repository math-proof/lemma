import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Ideal.Counting
open scoped NumberField
open NumberField
open Ideal


/--
[card_nonzero_absNorm_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean)
-/
@[path]
private lemma card_nonzero_absNorm_le_eq
  [Field K] [NumberField K]
  {M : ℕ} :
-- imply
  Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} ≤
    (Module.finrank ℚ K * M) ^ Nat.log 2 M := by
-- proof
  apply NumberField.Ideal.card_nonzero_absNorm_le K M

/--
[card_nonzero_absNorm_le_real](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean)
-/
@[path]
private lemma card_nonzero_absNorm_le_real_eq
  [Field K] [NumberField K]
  {M : ℝ} :
-- imply
  Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} ≤
    (Module.finrank ℚ K * ⌊M⌋₊) ^ Nat.log 2 ⌊M⌋₊ := by
-- proof
  apply NumberField.Ideal.card_nonzero_absNorm_le_real K M

/--
[card_nonzero_absNorm_le_real_rpow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean)
-/
@[path]
private lemma card_nonzero_absNorm_le_real_rpow_eq
  [Field K] [NumberField K]
  {M : ℝ}
-- given
  (hM : 0 < M) :
-- imply
  (Nat.card {I : Ideal (𝓞 K) //
    I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} : ℝ) ≤
    ((Module.finrank ℚ K : ℝ) * M) ^ (Real.logb 2 M) := by
-- proof
  apply NumberField.Ideal.card_nonzero_absNorm_le_real_rpow K M hM


-- created on 2026-10-20
