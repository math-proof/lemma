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
import Def.NumberTheory.Sequences.GeneralizedEuclidSequence.Part7
/-!
# Generalized Euclid sequences contain every prime

This file proves that every finite prime seed extends to an injective generalized Euclid
sequence containing every prime.
-/


namespace MetaMathlibExt

open scoped Pointwise

theorem chainL_succ (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    chainL P hP (n + 1) =
      Classical.choose (prop_reach P (chainL P hP n) (chainL_good P hP n)) := by
  simp only [chainL, Chain, chainStep]

theorem chainL_step (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    chainL P hP n <+: chainL P hP (n + 1) := by
  have h := (Classical.choose_spec
    (prop_reach P (chainL P hP n) (chainL_good P hP n))).1
  rw [← chainL_succ P hP n] at h
  exact h

theorem chainL_lt (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    (chainL P hP n).length < (chainL P hP (n + 1)).length := by
  have h := (Classical.choose_spec
    (prop_reach P (chainL P hP n) (chainL_good P hP n))).2.1
  rw [← chainL_succ P hP n] at h
  exact h

theorem chainL_qmem (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    sInf {p | p.Prime ∧ p ∉ chainL P hP n} ∈ chainL P hP (n + 1) := by
  have h := (Classical.choose_spec
    (prop_reach P (chainL P hP n) (chainL_good P hP n))).2.2.2
  rw [← chainL_succ P hP n] at h
  exact h

theorem chainL_spec (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    chainL P hP n <+: chainL P hP (n + 1) ∧
      (chainL P hP n).length < (chainL P hP (n + 1)).length ∧
      sInf {p | p.Prime ∧ p ∉ chainL P hP n} ∈ chainL P hP (n + 1) :=
  ⟨chainL_step P hP n, chainL_lt P hP n, chainL_qmem P hP n⟩

theorem chainL_prefix_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (s t : ℕ)
    (h : s ≤ t) : chainL P hP s <+: chainL P hP t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact List.prefix_refl _
  | succ k ih => exact ih.trans (chainL_step P hP _)

theorem chainL_len (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    P.card + n ≤ (chainL P hP n).length := by
  induction n with
  | zero => simp [chainL, Chain, Finset.length_toList]
  | succ n ih =>
    have hlt := (chainL_spec P hP n).2.1
    omega

theorem chainL_eval_stable (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (i s t : ℕ)
    (hs : i < (chainL P hP s).length) (hst : s ≤ t) :
    eVal (chainL P hP s) i = eVal (chainL P hP t) i :=
  eVal_prefix _ _ (chainL_prefix_le P hP s t hst) i hs

end MetaMathlibExt
