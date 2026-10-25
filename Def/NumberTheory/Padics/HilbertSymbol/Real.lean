/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Real.lean -/

import Def.NumberTheory.Padics.HilbertSymbol
import Lemma.Nat.Padics.HilbertSymbol
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false

/-!
# The real Hilbert symbol

This file defines the Hilbert symbol on nonzero real numbers through solvability of the
associated binary quadratic equation, and characterizes it by signs.
-/


/-- The real Hilbert symbol, defined by solvability of
`a * x ^ 2 + b * y ^ 2 = 1` over `ℝ`. -/
noncomputable def realHilbertSymbol (a b : ℝˣ) : ℤ :=
  hilbertSymbol ℝ a b

