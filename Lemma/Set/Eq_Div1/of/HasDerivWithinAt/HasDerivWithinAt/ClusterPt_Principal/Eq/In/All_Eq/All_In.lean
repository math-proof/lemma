import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_10_4
open Chapter9
open Chapter10
open HasDerivWithinAt


/--
[_root_.HasDerivWithinAt.of_inverse'](https://github.com/teorth/analysis/blob/main/Analysis/Section_10_4.lean)
-/
@[path]
private lemma main
  {X Y: Set ℝ}
  {f g : ℝ → ℝ}
  {x₀ y₀ f'x₀ g'y₀: ℝ}
-- given
  (hfXY: ∀ x ∈ X, f x ∈ Y)
  (hgf: ∀ x ∈ X, g (f x) = x)
  (hx₀: x₀ ∈ X)
  (hfx₀: f x₀ = y₀)
  (hcluster: ClusterPt x₀ (.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f f'x₀ X x₀)
  (hg: HasDerivWithinAt g g'y₀ Y y₀) :
-- imply
  g'y₀ = 1/f'x₀ :=
-- proof
  HasDerivWithinAt.of_inverse' hfXY hgf hx₀ hfx₀ hcluster hf hg


-- created on 2026-10-22
