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
import Theorem.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part7


section

namespace MetaMathlibExt

open PowerSeries

open scoped PowerSeries.WithPiTopology

/-- The off-diagonal part of `opcT M` is the support of `b * c`. -/
def opcPart2 (M : ℕ) :
    {t : opcT M // ¬ (5 : ℤ) ∣ t.val.2} ≃
      opcSq (fun x => x % 5 = 1 ∨ x % 5 = 4)
        (fun x => x % 5 = 2 ∨ x % 5 = 3) (5 * M) where
  toFun t := opcPart2Fwd M t.val.val.1 t.val.val.2
    t.val.property.1 t.val.property.2 t.property
  invFun s := opcPart2Bwd M s.val.1 s.val.2
    s.property.1 s.property.2.1 s.property.2.2
  left_inv t := by
    obtain ⟨⟨⟨x, y⟩, heq, hmod⟩, hny⟩ := t
    dsimp only
    by_cases hcase : y % 5 = 2 ∨ y % 5 = 3
    · rw [opcPart2Fwd_pos M x y heq hmod hny hcase,
        opcPart2Bwd_pos M x y _ _ heq hmod]
    · have hneg : ¬ ((y : ZMod 5)) = 3 * ((x : ZMod 5)) := by
        intro hcon
        exact hny (opc_no_collide x y hmod hcon)
      rw [opcPart2Fwd_neg M x y heq hmod hny hcase,
        opcPart2Bwd_neg M y x _ _ _ hneg]
  right_inv s := by
    obtain ⟨⟨a, b⟩, ha, hb, heq⟩ := s
    dsimp only
    by_cases h : ((a : ZMod 5)) = 3 * ((b : ZMod 5))
    · rw [opcPart2Bwd_pos M a b ha hb heq h,
        opcPart2Fwd_pos M a b heq h _ hb]
    · have hneg : ¬ (a % 5 = 2 ∨ a % 5 = 3) := by omega
      rw [opcPart2Bwd_neg M a b ha hb heq h,
        opcPart2Fwd_neg M b a _ _ _ hneg]

end MetaMathlibExt
end
