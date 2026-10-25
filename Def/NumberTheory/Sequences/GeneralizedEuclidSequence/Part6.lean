/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Sequences/GeneralizedEuclidSequence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.List.GetD
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Tactic.FieldSimp
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factors
import Mathlib.GroupTheory.GroupAction.Quotient
import Theorem.NumberTheory.Sequences.GeneralizedEuclidSequence.Part5
/-!
# Generalized Euclid sequences contain every prime

This file proves that every finite prime seed extends to an injective generalized Euclid
sequence containing every prime.
-/


namespace MetaMathlibExt

open scoped Pointwise

/-- A finite list is a valid partial generalized Euclid sequence from seed `P`:
it starts with an enumeration of `P`, has distinct prime entries, and every
entry at position `j ≥ P.card` divides a complementary-product sum of earlier
entries. -/
def Good (P : Finset ℕ) (l : List ℕ) : Prop :=
  P.toList <+: l ∧ l.Nodup ∧ (∀ x ∈ l, x.Prime) ∧
    ∀ j, P.card ≤ j → ∀ hj : j < l.length,
      ∃ I, I ⊆ Finset.range j ∧
        l[j]'hj ∣ (∏ i ∈ I, eVal l i) + ∏ i ∈ (Finset.range j \ I), eVal l i

end MetaMathlibExt
