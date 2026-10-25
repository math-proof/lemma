/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry5Corollary.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Corollary to Entry 5

Series for (1/2)log 3+(1/3)log 4-1 via 2/(216n³-6n).
-/


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry5Corollary

noncomputable def auxHR (m : ℕ) : ℝ := ∑ k ∈ Finset.range m, (1 : ℝ) / ((k : ℝ) + 1)

end Entry5Corollary
end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
