/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10Zeta2.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Def.Analysis.Ramanujan.Part1Ch7Entry10ZetaSide
public import Theorem.Real.Ramanujan.Part1Ch7Entry10ZetaSide
public import Theorem.Complex.Part1Ch7PowerDifference
public import Def.Analysis.Ramanujan.Part1Ch7PowerDifference
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Meromorphic.Complex
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.Topology.Separation.CompletelyRegular
public import Def.Analysis.Ramanujan.Part1Ch7Entry10Zeta2
@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 10

Power-sum distribution relation equals (1-nʳ⁺¹)ζ(-r) meromorphically.
-/


namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry10Zeta2

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

/-- Compatibility alias for the former `Entry10Zeta2.chapter7PowerDifferenceTerm`.

For new code, use `MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm`
directly. -/
noncomputable abbrev chapter7PowerDifferenceTerm (r x : ℂ) (j : ℕ) : ℂ :=
  MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm r x j

end Entry10Zeta2
end MathlibExt.Analysis.Ramanujan.Part1Ch7
