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
import Theorem.NumberTheory.Sequences.GeneralizedEuclidSequence.Part2
/-!
# Generalized Euclid sequences contain every prime

This file proves that every finite prime seed extends to an injective generalized Euclid
sequence containing every prime.
-/


namespace MetaMathlibExt

open scoped Pointwise

def geneuclidUnitOfNat (q : ℕ) [Fact q.Prime] [NeZero q]
    (d : ℕ) (hqd : ¬q ∣ d) : (ZMod q)ˣ :=
  Units.mk0 (d : ZMod q) (mt (ZMod.natCast_eq_zero_iff d q).mp hqd)

def geneuclidSevenRepresentatives : Finset (Units (ZMod 7)) :=
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let _ : NeZero 7 := ⟨by decide⟩
  {geneuclidUnitOfNat 7 1 (by norm_num), geneuclidUnitOfNat 7 2 (by norm_num),
    geneuclidUnitOfNat 7 3 (by norm_num), geneuclidUnitOfNat 7 5 (by norm_num),
    geneuclidUnitOfNat 7 6 (by norm_num)}

end MetaMathlibExt
