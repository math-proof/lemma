/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry12.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

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
