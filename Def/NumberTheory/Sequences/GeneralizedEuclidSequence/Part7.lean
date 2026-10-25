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
import Theorem.NumberTheory.Sequences.GeneralizedEuclidSequence.Part6
/-!
# Generalized Euclid sequences contain every prime

This file proves that every finite prime seed extends to an injective generalized Euclid
sequence containing every prime.
-/


namespace MetaMathlibExt

open scoped Pointwise

/-- One stage of the construction: adjoin the smallest missing prime. -/
noncomputable def chainStep (P : Finset ℕ) (x : { l : List ℕ // Good P l }) :
    { l : List ℕ // Good P l } :=
  ⟨Classical.choose (prop_reach P x.1 x.2),
    (Classical.choose_spec (prop_reach P x.1 x.2)).2.2.1⟩

/-- The nested tower of partial sequences. -/
noncomputable def Chain (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ℕ → { l : List ℕ // Good P l }
  | 0 => ⟨P.toList, good_nil P hP⟩
  | n + 1 => chainStep P (Chain P hP n)

noncomputable def chainL (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) : List ℕ :=
  (Chain P hP n).1

end MetaMathlibExt
