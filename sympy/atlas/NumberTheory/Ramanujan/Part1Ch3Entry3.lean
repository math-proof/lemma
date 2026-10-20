/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry3.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Defs.Filter
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry9Odd
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Asymptotics.Arith
import Mathlib.Analysis.Asymptotics.Basic
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Basic

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10Example4HarmonicPoissonAsymptotic

end Entry10Example4HarmonicPoissonAsymptotic

namespace Entry3

noncomputable def sector (ε : ℝ) : Set ℂ :=
  {z : ℂ | -Real.pi + ε ≤ Complex.arg z ∧ Complex.arg z ≤ Real.pi - ε}

noncomputable def fCoeff (x : ℂ) (j : ℕ) : ℂ :=
  Complex.exp (-x) * ∑' (k : ℕ), (((k + 1 : ℕ) : ℂ) ^ j * x ^ (k + 1) / (Nat.factorial k : ℂ))

noncomputable def psi (x z : ℂ) : ℂ :=
  ∑' (j : ℕ), if ∏ i ∈ Finset.range (j + 1), (z + ((i + 1 : ℕ) : ℂ)) = (0 : ℂ) then (0 : ℂ) else
      ((-1 : ℂ) ^ j * x ^ (j + 1) / ∏ i ∈ Finset.range (j + 1), (z + ((i + 1 : ℕ) : ℂ)))

/-- `fCoeff` is the `a = 0, b = 1` case of Ramanujan's generalized Bell function. -/
theorem fCoeff_eq_generalizedBellGenerating (x : ℂ) (j : ℕ) :
    fCoeff x j =
      Entry9IiGeneralizedbellgeneratingDefining.generalizedBellGenerating 0 1 x j := by
  unfold fCoeff
    Entry9IiGeneralizedbellgeneratingDefining.generalizedBellGenerating
  congr 1
  apply tsum_congr
  intro k
  simp only [zero_add, one_mul]

/-- The Entry 9 product with `a = 0, b = 1` coincides with the Entry 3 product. -/
private lemma prod_entry9_eq (z : ℂ) (j : ℕ) :
    (∏ r ∈ Finset.range (j + 1), (z + (0 : ℂ) + (1 : ℂ) * ((r : ℂ) + 1)))
      = ∏ i ∈ Finset.range (j + 1), (z + ((i + 1 : ℕ) : ℂ)) := by
  apply Finset.prod_congr rfl
  intro r _
  have hcast : (((r + 1 : ℕ)) : ℂ) = (r : ℂ) + 1 := by push_cast; ring
  rw [hcast]
  ring

/-- `psi` is pointwise `entry9_P 0 1`: the guard in `psi` is redundant because
complex division by zero is already zero. -/
theorem psi_eq_entry9_P (x z : ℂ) :
    psi x z = Entry9Odd.entry9_P 0 1 x z := by
  unfold psi Entry9Odd.entry9_P
  apply tsum_congr
  intro j
  have hprod := prod_entry9_eq z j
  by_cases h : ∏ i ∈ Finset.range (j + 1), (z + ((i + 1 : ℕ) : ℂ)) = 0
  · have h2 : ∏ r ∈ Finset.range (j + 1), (z + (0 : ℂ) + (1 : ℂ) * ((r : ℂ) + 1)) = 0 :=
      hprod.trans h
    rw [ite_eq_left h, h2]
    simp
  · rw [ite_eq_right h, ← hprod]

/-- `ramanujan_part1_ch3_entry3` without the hypothesis `x ≠ 0`. It follows from
`Entry9Odd.ramanujan_part1_ch3_entry9_odd` with `a = 0, b = 1`, which has no nonzero
hypothesis on `x`. -/
theorem ramanujan_part1_ch3_entry3_general (x : ℂ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < Real.pi) (N : ℕ) :
    Asymptotics.IsBigO (Filter.cocompact ℂ ⊓ Filter.principal (sector ε))
      (fun z : ℂ => psi x z - ∑ j ∈ Finset.range (N + 1), ((-1 : ℂ) ^ j * fCoeff x j / z ^ (j + 1)))
      (fun z : ℂ => (1 : ℂ) / z ^ (N + 2)) := by
  have h9 :=
    Entry9Odd.ramanujan_part1_ch3_entry9_odd 0 1 x one_ne_zero ε hε_pos hε_lt N
  have hfun : (fun z : ℂ => (z + (0 : ℂ)) / (1 : ℂ)) = id := by
    funext z
    simp
  have hfilter :
      Filter.comap (fun z : ℂ => (z + (0 : ℂ)) / (1 : ℂ))
          (Filter.cocompact ℂ ⊓ Filter.principal
            {w : ℂ | -Real.pi + ε ≤ Complex.arg w ∧ Complex.arg w ≤ Real.pi - ε})
        = Filter.cocompact ℂ ⊓ Filter.principal (sector ε) := by
    rw [hfun, Filter.comap_id]
    rfl
  rw [hfilter] at h9
  have hsum : ∀ z : ℂ, (Finset.sum (Finset.range (N + 1)) (fun k : ℕ =>
      ((-1 : ℂ) ^ k *
        Entry9IiGeneralizedbellgeneratingDefining.generalizedBellGenerating 0 1 x k)
        / z ^ (k + 1)))
      = ∑ j ∈ Finset.range (N + 1), ((-1 : ℂ) ^ j * fCoeff x j / z ^ (j + 1)) := by
    intro z
    apply Finset.sum_congr rfl
    intro j _
    simp only [fCoeff_eq_generalizedBellGenerating]
  have hLHS :
      (fun z : ℂ => psi x z -
        ∑ j ∈ Finset.range (N + 1), ((-1 : ℂ) ^ j * fCoeff x j / z ^ (j + 1)))
      = fun z : ℂ => -((Finset.sum (Finset.range (N + 1)) (fun k : ℕ =>
          ((-1 : ℂ) ^ k *
            Entry9IiGeneralizedbellgeneratingDefining.generalizedBellGenerating 0 1 x k)
            / z ^ (k + 1)) - Entry9Odd.entry9_P 0 1 x z)) := by
    funext z
    rw [← psi_eq_entry9_P, hsum z]
    ring
  rw [hLHS]
  exact h9.neg_left

/-- Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 3, printed p. 47 / PDF p.
    57.

Proves `Wanted` entry `ramanujan_part1_ch3_entry3`. It follows from
`ramanujan_part1_ch3_entry3_general`; the hypothesis `x ≠ 0` is unused and keeps the
source's shape.
-/
theorem ramanujan_part1_ch3_entry3 (x : ℂ)
    (hx : x ≠ 0) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < Real.pi) (N : ℕ) :
    Asymptotics.IsBigO (Filter.cocompact ℂ ⊓ Filter.principal (sector ε))
      (fun z : ℂ => psi x z - ∑ j ∈ Finset.range (N + 1), ((-1 : ℂ) ^ j * fCoeff x j / z ^ (j + 1)))
      (fun z : ℂ => (1 : ℂ) / z ^ (N + 2)) := by
  have _ : x ≠ 0 := hx
  exact ramanujan_part1_ch3_entry3_general x ε hε_pos hε_lt N

end Entry3

namespace Entry3Fsummable

end Entry3Fsummable

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
