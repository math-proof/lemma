/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/ODE/PicardIteration.lean -/


import Theorem.Analysis.ODE.PicardIteration


namespace MetaMathlibExt

open MeasureTheory MathlibExt.Analysis.ODE.PicardIterationWanted

/-- Picard iterates for `x' = 1` from the constant zero initial map. -/
def constU : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | _ + 1 => fun s => s

end MetaMathlibExt
