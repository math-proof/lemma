import Mathlib
import Notation.Algebra.Power
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.TwoPointDerivCompute
open Real Set BooleanFourier


/--
[twoPointLogPathFn_eq_log](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/TwoPointDerivCompute.lean)
-/
@[path]
private lemma main
  {p a b t : ℝ}
-- given
  (hp : p > 1)
  (ha : a > 0)
  (hb : b > 0)
  (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
-- imply
  twoPointLogPathFn p a b t = Real.log (((((1 + t) / 2 * a + (1 - t) / 2 * b) ^ (1 + (p - 1) / t²) + ((1 - t) / 2 * a + (1 + t) / 2 * b) ^ (1 + (p - 1) / t²)) / 2) ^ (1 / (1 + (p - 1) / t²))) := by
-- proof
  unfold twoPointLogPathFn
  simp only
  set r := 1 + (p - 1) / t²
  set c := (1 + t) / 2 * a + (1 - t) / 2 * b
  set d := (1 - t) / 2 * a + (1 + t) / 2 * b
  have hr_pos : (0 : ℝ) < r := by
    have : 0 < (p - 1) / t² := div_pos (by linarith [hp]) (sq_pos_of_pos ht.1)
    linarith
  have hc_pos : (0 : ℝ) < c :=
    add_pos (mul_pos (by linarith [ht.1]) ha) (mul_pos (by linarith [ht.2]) hb)
  have hd_pos : (0 : ℝ) < d :=
    add_pos (mul_pos (by linarith [ht.2]) ha) (mul_pos (by linarith [ht.1]) hb)
  have hS_pos : (0 : ℝ) < (c ^ r + d ^ r) / 2 :=
    div_pos (add_pos_of_pos_of_nonneg (rpow_pos_of_pos hc_pos r)
      (rpow_nonneg hd_pos.le r)) two_pos
  rw [Real.log_rpow hS_pos]


lemma BooleanFourier.twoPointLogPathFn_eq_log
  {p a b t : ℝ}
-- given
  (hp : p > 1)
  (ha : a > 0)
  (hb : b > 0)
  (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
-- imply
  twoPointLogPathFn p a b t = Real.log (((((1 + t) / 2 * a + (1 - t) / 2 * b) ^ (1 + (p - 1) / t²) + ((1 - t) / 2 * a + (1 + t) / 2 * b) ^ (1 + (p - 1) / t²)) / 2) ^ (1 / (1 + (p - 1) / t²))) :=
-- proof
  main hp ha hb ht


-- created on 2026-10-23
-- updated on 2026-11-24
