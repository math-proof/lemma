/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Multiset.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Def.Combinatorics.Enumerative.Partition.Overpartition
import Lemma.Nat.Enumerative.Partition.Overpartition
import Lemma.Nat.QuadraticForms.ThreeSquares
import Lemma.Real.SpecialFunctions.JacobiTripleProduct
import Def.NumberTheory.QuadraticForms.ThreeSquares
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Def.Analysis.SpecialFunctions.JacobiTripleProduct
import Theorem.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part5


section

namespace MetaMathlibExt

open PowerSeries

open scoped PowerSeries.WithPiTopology

/-- Forward map for the off-diagonal part: identity when `y ≡ ±2`,
swap when `y ≡ ±1`. -/
def opcPart2Fwd (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ))
    (_hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5))) (hny : ¬ (5 : ℤ) ∣ y) :
    opcSq (fun x => x % 5 = 1 ∨ x % 5 = 4)
      (fun x => x % 5 = 2 ∨ x % 5 = 3) (5 * M) := by
  refine dite (y % 5 = 2 ∨ y % 5 = 3) (fun hcase => ?_) (fun hcase => ?_)
  · exact ⟨(x, y), opc_fwd_mem_left M x y heq hcase, hcase, heq⟩
  · exact ⟨(y, x), opc_fwd_mem_y y hny hcase,
      opc_fwd_mem_right M x y heq (opc_fwd_mem_y y hny hcase),
      opc_fwd_eq_swap M x y heq⟩

end MetaMathlibExt
end
