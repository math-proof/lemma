import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.Analysis.ODE.PicardIteration
open MeasureTheory MathlibExt.Analysis.ODE.PicardIterationWanted


namespace MetaMathlibExt

/--
[constU_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/ODE/PicardIteration.lean)
-/
@[path]
private lemma constU_zero : constU 0 = fun _ => (0 : ℝ) :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[constU_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/ODE/PicardIteration.lean)
-/
@[path]
private lemma constU_step (n : ℕ) (t : ℝ) :
  constU (n + 1) t =
    0 + ∫ s in (0 : ℝ)..t, (1 : ℝ) := by
  simp [constU, intervalIntegral.integral_const]

end MetaMathlibExt


-- created on 2026-10-23
