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
import Def.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part5


section

namespace MetaMathlibExt

open PowerSeries

open scoped PowerSeries.WithPiTopology

/-- The cast equation in `ZMod 5`. -/
theorem opc_fwd_hXY (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ)) :
    ((x : ZMod 5)) ^ 2 + ((y : ZMod 5)) ^ 2 = 0 := by
  have hcast : ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5)
      = ((((5 * M : ℕ))) : ZMod 5) := by rw [heq, Int.cast_natCast]
  have h0 : ((((5 * M : ℕ))) : ZMod 5) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_mul_right 5 M)
  rw [h0] at hcast
  have hpush : ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5)
      = ((x : ZMod 5)) ^ 2 + ((y : ZMod 5)) ^ 2 := by push_cast; ring
  rw [hpush] at hcast
  exact hcast

/-- Negated form of the cast equation. -/
theorem opc_fwd_hneg (x y : ℤ)
    (hXY : ((x : ZMod 5)) ^ 2 + ((y : ZMod 5)) ^ 2 = 0) :
    ((x : ZMod 5)) ^ 2 = -((y : ZMod 5)) ^ 2 := by
  linear_combination hXY

/-- From the equation and `y ≡ ±2`, get `x ≡ ±1`. -/
theorem opc_fwd_mem_left (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ))
    (hcase : y % 5 = 2 ∨ y % 5 = 3) : x % 5 = 1 ∨ x % 5 = 4 := by
  have hneg := opc_fwd_hneg x y (opc_fwd_hXY M x y heq)
  have hy2 : ((y : ZMod 5)) ^ 2 = 4 := by
    have hsq := opc_sq_four y hcase
    have hpush : ((((y ^ 2 : ℤ))) : ZMod 5) = ((y : ZMod 5)) ^ 2 := by
      push_cast; ring
    rw [← hpush]
    exact hsq
  have hx2 : ((x : ZMod 5)) ^ 2 = 1 := by
    rw [hneg, hy2]
    decide
  exact opc_mem_pm1 x hx2

/-- Off multiples of 5 and outside `±2`, the residue is `±1`. -/
theorem opc_fwd_mem_y (y : ℤ) (hny : ¬ (5 : ℤ) ∣ y)
    (_hcase : ¬ (y % 5 = 2 ∨ y % 5 = 3)) : y % 5 = 1 ∨ y % 5 = 4 := by
  omega

/-- From the equation and `y ≡ ±1`, get `x ≡ ±2`. -/
theorem opc_fwd_mem_right (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ))
    (hym : y % 5 = 1 ∨ y % 5 = 4) : x % 5 = 2 ∨ x % 5 = 3 := by
  have hneg := opc_fwd_hneg x y (opc_fwd_hXY M x y heq)
  have hy2 : ((y : ZMod 5)) ^ 2 = 1 := by
    have hsq := opc_sq_one y hym
    have hpush : ((((y ^ 2 : ℤ))) : ZMod 5) = ((y : ZMod 5)) ^ 2 := by
      push_cast; ring
    rw [← hpush]
    exact hsq
  have hx2 : ((x : ZMod 5)) ^ 2 = 4 := by
    rw [hneg, hy2]
    decide
  exact opc_mem_pm2 x hx2

/-- The swapped equation. -/
theorem opc_fwd_eq_swap (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ)) :
    y ^ 2 + x ^ 2 = (((5 * M : ℕ)) : ℤ) := by
  linear_combination heq

end MetaMathlibExt
end
