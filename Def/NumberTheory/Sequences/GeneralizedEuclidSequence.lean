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
/-!
# Generalized Euclid sequences contain every prime

This file proves that every finite prime seed extends to an injective generalized Euclid
sequence containing every prime.
-/


namespace MetaMathlibExt

open scoped Pointwise

/-- Value of the `i`-th entry of a list, defaulting to `0` out of range. -/
def eVal (l : List ℕ) (i : ℕ) : ℕ := l.getD i 0

def geneuclidProduct (l : List ℕ) : ℕ :=
  ∏ i ∈ Finset.range l.length, eVal l i

def geneuclidN (l : List ℕ) (I : Finset ℕ) : ℕ :=
  (∏ i ∈ I, eVal l i) + ∏ i ∈ (Finset.range l.length \ I), eVal l i

def GeneuclidAppendable (l : List ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ ∃ I ⊆ Finset.range l.length, p ∣ geneuclidN l I

def geneuclidResidues (q : ℕ) (l : List ℕ) : Finset (ZMod q) :=
  (Finset.range l.length).powerset.image fun I => ∏ i ∈ I, (eVal l i : ZMod q)

def geneuclidUnits (q : ℕ) [NeZero q] (l : List ℕ) : Finset (ZMod q)ˣ :=
  Finset.univ.filter fun u => (u : ZMod q) ∈ geneuclidResidues q l

end MetaMathlibExt
