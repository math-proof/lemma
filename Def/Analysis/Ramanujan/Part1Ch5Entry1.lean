/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry1.lean -/

/-
Author: @akiezun, Avocado
-/

import Def.Analysis.Ramanujan.Part1Ch5Entry1Euleriangf
import Lemma.Real.Part1Ch5Entry1Euleriangf
/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 1

Bernoulli numbers uniquely solve a shift-derivative operator identity.
-/


namespace MathlibExt.Analysis.Ramanujan.Part1Ch5

namespace Entry1

open scoped Nat Real BigOperators Interval Polynomial

open Filter Finset Complex Topology

open Entry1Euleriangf (chapter5DerivativeExpansion)

noncomputable section

def chapter5Entry1MinusCoeff (n : ℕ) : ℝ :=
  (bernoulli n : ℝ) / (n.factorial : ℝ)

def numE (a : ℕ → ℝ) (m : ℕ) (x h : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (m + 1), a n * h ^ n * (Nat.descFactorial m n : ℝ) * x ^ (m - n)

end
end Entry1
end MathlibExt.Analysis.Ramanujan.Part1Ch5
