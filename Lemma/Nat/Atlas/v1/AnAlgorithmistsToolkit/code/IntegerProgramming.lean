import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.IntegerProgramming
open Matrix Finset InnerProductSpace IntegerProgramming


namespace IntegerProgramming

/--
[layerSpacingBound_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/IntegerProgramming.lean)
-/
@[path]
lemma layerSpacingBound_pos
  {n : ℕ}
  {m : ℕ}
-- given
  (hm : 0 < m) :
-- imply
  0 < layerSpacingBound m := by
-- proof
  unfold layerSpacingBound
  apply mul_pos
  · exact Real.rpow_pos_of_pos (by norm_num : (2:ℝ) > 0) _
  · apply div_pos (by norm_num : (0:ℝ) < 2)
    exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)

end IntegerProgramming

namespace IntegerProgramming

/--
[layerCountBound_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/IntegerProgramming.lean)
-/
@[path]
lemma layerCountBound_pos
  {n : ℕ} :
-- imply
  ∀ k, 0 < layerCountBound k := by
-- proof
  intro k; unfold layerCountBound; split <;> omega

end IntegerProgramming

namespace IntegerProgramming

/--
[lenstraBound_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/IntegerProgramming.lean)
-/
@[path]
lemma lenstraBound_pos
  {n : ℕ} :
-- imply
  ∀ n, 0 < lenstraBound n := by
-- proof
  intro n
  induction n with
  | zero => simp [lenstraBound]
  | succ n ih =>
    unfold lenstraBound
    exact Nat.mul_pos (layerCountBound_pos _) ih

end IntegerProgramming

namespace IntegerProgramming

/--
[layerCountBound_ge_ceil_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/IntegerProgramming.lean)
-/
@[path]
lemma layerCountBound_ge_ceil_ratio
  {n : ℕ}
  {k : ℕ}
-- given
  (hk : 0 < k) :
-- imply
  (layerCountBound k : ℝ) ≥ 2 * fritzJohnRadius k / layerSpacingBound k := by
-- proof
  unfold layerCountBound
  simp [show k ≠ 0 from Nat.pos_iff_ne_zero.mp hk]
  have h1 : 2 * fritzJohnRadius k / layerSpacingBound k ≤
    (↑⌈2 * fritzJohnRadius k / layerSpacingBound k⌉₊ : ℝ) := Nat.le_ceil _
  linarith

end IntegerProgramming

namespace IntegerProgramming

/--
[candidateBox_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/IntegerProgramming.lean)
-/
@[path]
lemma candidateBox_card
  {n : ℕ}
  {n : ℕ} :
-- imply
  (candidateBox n).card = (2 * lenstraBound n + 1) ^ n := by
-- proof
  unfold candidateBox
  rw [Fintype.card_piFinset_const]
  congr 1; simp [Int.card_Icc]; omega

end IntegerProgramming

namespace IntegerProgramming

/--
[layerCountBound_le_lenstraBound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/IntegerProgramming.lean)
-/
@[path]
lemma layerCountBound_le_lenstraBound
  {n : ℕ}
  {k n : ℕ}
-- given
  (hk : k ≤ n) :
-- imply
  layerCountBound k ≤ lenstraBound n := by
-- proof
  induction n with
  | zero =>
    have : k = 0 := by omega
    subst this
    simp [layerCountBound, lenstraBound]
  | succ n ih =>
    simp only [lenstraBound]
    by_cases hkn : k ≤ n
    · calc layerCountBound k ≤ lenstraBound n := ih hkn
      _ ≤ layerCountBound (n + 1) * lenstraBound n :=
        Nat.le_mul_of_pos_left _ (layerCountBound_pos _)
    · have : k = n + 1 := by omega
      subst this
      exact Nat.le_mul_of_pos_right _ (lenstraBound_pos n)

end IntegerProgramming


-- created on 2026-10-23
