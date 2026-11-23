/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Separation.CompletelyRegular
public import Theorem.Analysis.SpecialFunctions.Part1Ch6Entry13Ramanujanfactorial.Part3

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 13

Two series in powers of x are summable and equal for |x|>1.
-/


namespace Ramanujan.Part1Ch6

namespace Entry13Ramanujanfactorial

open scoped Nat Real BigOperators Interval Polynomial

open Asymptotics Filter Finset Complex Topology

noncomputable section

noncomputable def Rdiff2 (x : ℕ × ℕ) : ℝ := wR x - (-1:ℝ)^(x.1+1)

end
end Entry13Ramanujanfactorial
end Ramanujan.Part1Ch6
