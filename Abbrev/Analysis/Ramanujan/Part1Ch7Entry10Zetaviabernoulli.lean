/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10Zetaviabernoulli.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Def.Analysis.Ramanujan.Part1Ch7PowerDifference
import Lemma.Complex.Part1Ch7PowerDifference
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.LSeries.Dirichlet
import Lemma.Nat.LSeries.RiemannZeta
import Def.Analysis.Ramanujan.Part1Ch7Entry10Zetaviabernoulli
/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 10, corollary

For `φ_r(x) = ∑_{j ≥ 0} ((j + 1)ʳ - (j + 1 + x)ʳ)`, `∑_{k=1}^{n-1} φ_r(-k/n) = (n - n⁻ʳ) ζ(-r)`
as meromorphic functions of `r`.
-/


namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry10Zetaviabernoulli

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

/-- Compatibility alias for the former `Entry10Zetaviabernoulli.chapter7Admissible`.

For new code, use `MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7Admissible` directly. -/
abbrev chapter7Admissible (x : ℂ) : Prop :=
  MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7Admissible x

/-- Compatibility alias for the former `Entry10Zetaviabernoulli.chapter7PowerDifferenceTerm`.

For new code, use `MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm`
directly. -/
noncomputable abbrev chapter7PowerDifferenceTerm (r x : ℂ) (j : ℕ) : ℂ :=
  MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm r x j

end Entry10Zetaviabernoulli
end MathlibExt.Analysis.Ramanujan.Part1Ch7
