/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry3Eulerianformula.lean -/

/-
Author: @akiezun, Avocado
-/

import sympy.atlas.Analysis.Ramanujan.Part1Ch5Entry8Eulerianformula
section
/-!
# Ramanujan's Notebooks, Part I, Chapter 5

Compatibility alias for Entry 8 (historically misnumbered as Entry 3); the
implementation lives in `Part1Ch5Entry8Eulerianformula.lean`.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch5

namespace Entry3Eulerianformula

open Entry4 Entry8Eulerianformula

noncomputable section

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5, Entry 8.

The theorem name preserves the historical misnumbering of this entry as Entry 3
(Entry 3 is `Entry3.ramanujan_part1_ch5_entry3`); the correctly named statement
is `Entry8Eulerianformula.ramanujan_part1_ch5_entry8_eulerianformula`, to which
this forwards.
-/
theorem ramanujan_part1_ch5_entry3_eulerianformula (n : ℕ) (z : ℂ)
    (hn : 1 ≤ n) (hz : ‖z‖ < Real.pi) :
    Complex.exp z + 1 ≠ 0 ∧
      chapter5Psi n (-1 : ℂ) = (n.factorial : ℂ) ∧
      chapter5Psi n (1 : ℂ) =
        (2 : ℂ) ^ (n + 1) * ((2 : ℂ) ^ (n + 1) - 1) *
          (bernoulli (n + 1) : ℂ) / (n + 1 : ℂ) ∧
      HasSum (chapter5Entry8BernoulliTerm z)
        (1 / (Complex.exp z + 1)) ∧
      HasSum (chapter5Entry8PsiTerm z)
        (1 / (Complex.exp z + 1)) :=
  Entry8Eulerianformula.ramanujan_part1_ch5_entry8_eulerianformula n z hn hz

end
end Entry3Eulerianformula
end MathlibExt.Analysis.Ramanujan.Part1Ch5
