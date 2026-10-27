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
/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 13

Two series in powers of x are summable and equal for |x|>1.
-/


namespace Ramanujan.Part1Ch6

namespace Entry13Ramanujanfactorial

open scoped Nat Real BigOperators Interval Polynomial

open Asymptotics Filter Finset Complex Topology

noncomputable section

noncomputable def signW (k : ℕ+) : ℝ := (-1 : ℝ) ^ ((k : ℕ) + 1)

noncomputable def dblL (t : ℝ) (c : ℕ+ × ℕ+) : ℝ :=
  signW c.1 * t ^ ((c.1 : ℕ) * (c.2 : ℕ))

end
end Entry13Ramanujanfactorial
end Ramanujan.Part1Ch6
