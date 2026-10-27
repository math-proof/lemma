import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[roth_abs_rat_le_of_approx](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {α p : ℝ}
  (q : ℚ)
-- given
  (hp : 0 < p)
  (hq : |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) p) :
-- imply
  |(q : ℝ)| ≤ |α| + 1 := by
-- proof
  have hden : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
  have hrpow : 1 ≤ Real.rpow (q.den : ℝ) p := Real.one_le_rpow hden hp.le
  have hrpow0 : 0 < Real.rpow (q.den : ℝ) p := Real.rpow_pos_of_pos (by positivity) _
  have hdist : |α - (q : ℝ)| < 1 := hq.trans_le ((div_le_one₀ hrpow0).2 hrpow)
  calc
    _ = |((q : ℝ) - α) + α| := by ring_nf
    _ ≤ |(q : ℝ) - α| + |α| := abs_add_le _ _
    _ ≤ 1 + |α| := by
      rw [abs_sub_comm]
      exact add_le_add hdist.le le_rfl
    _ = |α| + 1 := by ring


-- created on 2026-10-21
