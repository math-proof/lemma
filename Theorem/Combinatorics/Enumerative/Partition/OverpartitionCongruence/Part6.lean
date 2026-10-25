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
import Def.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part6


section

namespace MetaMathlibExt

open PowerSeries

open scoped PowerSeries.WithPiTopology

/-- Off `±1`, the second coordinate is not divisible by 5. -/
theorem opc_bwd_hn (b : ℤ) (hb : b % 5 = 2 ∨ b % 5 = 3) :
    ¬ (5 : ℤ) ∣ b := by
  omega

/-- Off `±2`, the first coordinate is not divisible by 5. -/
theorem opc_bwd_hna (a : ℤ) (ha : a % 5 = 1 ∨ a % 5 = 4) :
    ¬ (5 : ℤ) ∣ a := by
  omega

/-- The swapped-back equation. -/
theorem opc_bwd_eq_swap (M : ℕ) (a b : ℤ)
    (heq : a ^ 2 + b ^ 2 = (((5 * M : ℕ)) : ℤ)) :
    b ^ 2 + a ^ 2 = (((5 * M : ℕ)) : ℤ) := by
  linear_combination heq

/-- From residues and the negated equation, recover `b ≡ 3a`. -/
theorem opc_bwd_hba (a b : ℤ)
    (ha : a % 5 = 1 ∨ a % 5 = 4) (hb : b % 5 = 2 ∨ b % 5 = 3)
    (h : ¬ ((a : ZMod 5)) = 3 * ((b : ZMod 5))) :
    ((b : ZMod 5)) = 3 * ((a : ZMod 5)) := by
  rcases ha with ha1 | ha4 <;> rcases hb with hb2 | hb3
  · exfalso
    apply h
    have ea := opc_intCast_residue a 1 ha1
    have eb := opc_intCast_residue b 2 hb2
    rw [ea, eb]
    decide
  · have ea := opc_intCast_residue a 1 ha1
    have eb := opc_intCast_residue b 3 hb3
    rw [eb, ea]
    decide
  · have ea := opc_intCast_residue a 4 ha4
    have eb := opc_intCast_residue b 2 hb2
    rw [eb, ea]
    decide
  · exfalso
    apply h
    have ea := opc_intCast_residue a 4 ha4
    have eb := opc_intCast_residue b 3 hb3
    rw [ea, eb]
    decide

end MetaMathlibExt
end
