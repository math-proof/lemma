import Mathlib
import Notation.Algebra.Power
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.TwoPointDerivCompute.booleanFourier.twoPointLogPathFn_eq_log
open Real Set BooleanFourier Bool


/--
[twoPointLogPathFn_deriv_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/TwoPointDerivCompute.lean)
-/
@[path]
private lemma main
  {p a b t : ℝ}
-- given
  (hp : p > 1)
  (ht_pos : t > 0) :
-- imply
  twoPointLogPathFn_derivValue p a b t =
    (let r := 1 + (p - 1) / t²;
     let c := (1 + t) / 2 * a + (1 - t) / 2 * b;
     let d := (1 - t) / 2 * a + (1 + t) / 2 * b;
     let S := c ^ r + d ^ r;
     let r' := -2 * (p - 1) / t³;
     let c' := (a - b) / 2;
     let d' := (b - a) / 2;
     (c ^ (r - 1) * c' + d ^ (r - 1) * d') / S + r' / r * twoPointLogSumGap p a b t) := by
-- proof
  unfold twoPointLogPathFn_derivValue twoPointLogSumGap
  simp only
  set r := 1 + (p - 1) / t²
  have hr_ne : r ≠ 0 := by
    have : 0 < (p - 1) / t² := div_pos (by linarith [hp]) (sq_pos_of_pos ht_pos)
    linarith
  field_simp
  ring


lemma BooleanFourier.twoPointLogPathFn_deriv_decomp
  {p a b t : ℝ}
-- given
  (hp : p > 1)
  (ht_pos : t > 0) :
-- imply
  twoPointLogPathFn_derivValue p a b t =
    (let r := 1 + (p - 1) / t²;
     let c := (1 + t) / 2 * a + (1 - t) / 2 * b;
     let d := (1 - t) / 2 * a + (1 + t) / 2 * b;
     let S := c ^ r + d ^ r;
     let r' := -2 * (p - 1) / t³;
     let c' := (a - b) / 2;
     let d' := (b - a) / 2;
     (c ^ (r - 1) * c' + d ^ (r - 1) * d') / S + r' / r * twoPointLogSumGap p a b t) :=
-- proof
  main hp ht_pos


-- created on 2026-10-23
-- updated on 2026-11-24
