import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Padics.Strassmann
open Padic


/--
[strassmann](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Strassmann.lean)
-/
@[path]
private lemma strassmann_eq
  {p : ℕ} [Fact p.Prime]
  {b : ℕ → ℚ_[p]}
-- given
  (hb : Filter.Tendsto b Filter.cofinite (nhds 0))
  (hne : b ≠ 0) :
-- imply
  {y : ℚ_[p] | ‖y‖ ≤ 1 ∧ ∑' m, b m * y ^ m = 0}.Finite := by
-- proof
  apply Padic.strassmann p b hb hne


-- created on 2026-10-20
