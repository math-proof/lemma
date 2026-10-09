import sympy.core.power
import sympy.vector.Basic
import sympy.Basic
import stdlib.List
import Mathlib.MeasureTheory.Constructions.Polish.Basic
open MeasureTheory


/--
The discounted return `((γ ^ (id : ℕ → ℕ)) @ r[t:])` is measurable when each reward `r t` is.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {r : ℕ → Ω → ℝ}
-- given
  (hr : ∀ t, Measurable (r t))
  (γ : ℝ)
  (t : ℕ) :
-- imply
  Measurable ((γ ^ (id : ℕ → ℕ)) @ r[t:]) :=
-- proof
  Measurable.tsum fun k => (hr (t + k)).const_mul (γ ^ k)


-- created on 2026-10-09
