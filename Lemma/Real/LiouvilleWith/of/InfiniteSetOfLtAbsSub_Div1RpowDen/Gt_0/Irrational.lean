import Mathlib
import sympy.Basic
import Lemma.Real.Any_LtAbsSub_Div1RpowDenAndLt_Den.of.InfiniteSetOfLtAbsSub_Div1RpowDen.Gt_0
open Real


/--
[roth_liouvilleWith_of_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {α p : ℝ}
-- given
  (hα : Irrational α)
  (hp : 0 < p)
  (hinf : Set.Infinite {q : ℚ |
    |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) p}) :
-- imply
  LiouvilleWith p α := by
-- proof
  refine ⟨1, Filter.frequently_atTop.2 fun N ↦ ?_⟩
  obtain ⟨q, hq, hN⟩ :=
    Any_LtAbsSub_Div1RpowDenAndLt_Den.of.InfiniteSetOfLtAbsSub_Div1RpowDen.Gt_0 N hp hinf
  refine ⟨q.den, hN.le, q.num, ?_, ?_⟩
  ·
    simpa only [Rat.cast_def] using hα.ne_rat q
  ·
    change |α - (q.num : ℝ) / q.den| < 1 / Real.rpow (q.den : ℝ) p
    simpa only [Rat.cast_def] using hq


-- created on 2026-10-21
