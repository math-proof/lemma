module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.Analysis.Ramanujan.Part1Ch9Entry16Tanseries
public import Theorem.Real.Ramanujan.Part1Ch9Entry16Tanseries


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry31Ramanujansum.lean -/
/-
Author: @akiezun, Avocado
-/
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/
section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry31Ramanujansum

noncomputable section

def chapter9PsiTerm (x : ℝ) (k : ℕ) : ℝ :=
  (Nat.choose (2 * k) k : ℝ) *
      Real.sin (Real.pi * x) ^ (2 * k + 1) /
    ((2 : ℝ) ^ (2 * k) * (((2 * k + 1 : ℕ) : ℝ) ^ 2))

end
end Entry31Ramanujansum
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
