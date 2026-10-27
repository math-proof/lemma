/-
Author: @akiezun, Avocado
-/

import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular
import Theorem.Analysis.SpecialFunctions.Part1Ch6Entry13Ramanujanfactorial.Part2
/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 13

Two series in powers of x are summable and equal for |x|>1.
-/


namespace Ramanujan.Part1Ch6

namespace Entry13Ramanujanfactorial

open scoped Nat Real BigOperators Interval Polynomial

open Asymptotics Filter Finset Complex Topology

noncomputable section

noncomputable def wR (p : ℕ × ℕ) : ℝ :=
  if p.2 % 2 = p.1 % 2 ∧ p.1 ≤ p.2 then
    (if p.1 = p.2 then (-1:ℝ)^(p.1+1) else 2 * (-1:ℝ)^(p.1+1))
  else 0

noncomputable def Rcoeff (N : ℕ) : ℝ := ∑ x ∈ N.divisorsAntidiagonal, wR x

end
end Entry13Ramanujanfactorial
end Ramanujan.Part1Ch6
