/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry14Xoversin.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry13Bernoulligen
import Lemma.Real.Part1Ch9Entry13Bernoulligen
section
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry14Xoversin

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen

noncomputable section

def chapter9ChiAtOne (m : ℕ) : ℝ :=
  ∑' k : ℕ, 1 / (((2 * k + 1 : ℕ) : ℝ) ^ m)

def chapter9Entry14Integrand (n : ℕ) (u : ℝ) : ℝ :=
  u ^ n / 2 / Real.sin u

def chapter9OddClausenTerm (m : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  let odd : ℕ := 2 * k + 1
  if Even m then
    Real.sin ((odd : ℝ) * x) / ((odd : ℝ) ^ m)
  else
    Real.cos ((odd : ℝ) * x) / ((odd : ℝ) ^ m)

def chapter9OddClausen (m : ℕ) (x : ℝ) : ℝ :=
  if m = 0 then 0
  else if m = 1 then -(1 / 2 : ℝ) * Real.log |Real.tan (x / 2)|
  else ∑' k : ℕ, chapter9OddClausenTerm m x k
end
end Entry14Xoversin
end MathlibExt.Analysis.Ramanujan.Part1Ch9
