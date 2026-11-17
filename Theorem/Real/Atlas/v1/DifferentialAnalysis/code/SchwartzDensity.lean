module

public import Mathlib
public import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzDensity

public section

open SchwartzDensity
open scoped ENNReal
open MeasureTheory


namespace SchwartzDensity

/--
[schwartz_dense_Lp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzDensity.lean)
-/
public theorem schwartz_dense_Lp
  {n : ℕ}
  {p : ENNReal}
  [Fact (1 ≤ p)]
-- given
  (hp : p ≠ ⊤) :
-- imply
  DenseRange (SchwartzMap.toLpCLM (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) ℂ p volume) :=
-- proof
  SchwartzMap.denseRange_toLpCLM hp
end SchwartzDensity



-- created on 2026-10-23
