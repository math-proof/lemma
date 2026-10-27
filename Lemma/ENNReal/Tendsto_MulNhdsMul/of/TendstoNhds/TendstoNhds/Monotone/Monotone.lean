import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.MeasureTheory.Notation.Part2
open Filter
open ENNReal


/--
[ENNReal.upward_continuous](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Notation.lean)
-/
@[path]
private lemma main
  {x y:ℕ → ENNReal}
  {x₀ y₀ : ENNReal}
-- given
  (hx: Monotone x)
  (hy: Monotone y)
  (hx_lim: atTop.Tendsto x (nhds x₀))
  (hy_lim: atTop.Tendsto y (nhds y₀)) :
-- imply
  atTop.Tendsto (fun n ↦ x n * y n) (nhds (x₀ * y₀)) :=
-- proof
  ENNReal.upward_continuous hx hy hx_lim hy_lim


-- created on 2026-10-22
