import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevDuality
open Real MeasureTheory MeasureTheory.Measure TestFunctions SobolevDuality
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap
open TestFunctions


namespace SobolevDuality

/--
[sobolevWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDuality.lean)
-/
@[path]
lemma sobolevWeight_pos
  {n : ℕ}
  {s : ℝ}
  {ξ : EuclideanSpace ℝ (Fin n)} :
-- imply
  0 < sobolevWeight n s ξ :=
-- proof
  Real.rpow_pos_of_pos (japaneseBracket_pos n ξ) s

end SobolevDuality


-- created on 2026-10-23
