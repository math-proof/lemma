/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry12.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lemma.Nat.Ramanujan.Part1Ch3Entry12SummableSuccN
/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 12

Recurrence F(r+1, n) = n F(r, n) + F(r+1, n+1)/a for ∑ (n+k)^(r+k)/(aᵏ k!).
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry12

noncomputable def F (r : ℤ) (n a : ℂ) : ℂ :=
  ∑' k : ℕ, (n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (k.factorial : ℂ))
end Entry12
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
