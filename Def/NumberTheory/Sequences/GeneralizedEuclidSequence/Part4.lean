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
import Theorem.NumberTheory.Sequences.GeneralizedEuclidSequence.Part3
/-!
# Generalized Euclid sequences contain every prime

This file proves that every finite prime seed extends to an injective generalized Euclid
sequence containing every prime.
-/


namespace MetaMathlibExt

open scoped Pointwise

def geneuclidThirteenRepresentatives : Finset (Units (ZMod 13)) :=
  let _ : Fact (Nat.Prime 13) := ⟨by decide⟩
  let _ : NeZero 13 := ⟨by decide⟩
  {geneuclidUnitOfNat 13 1 (by norm_num), geneuclidUnitOfNat 13 15 (by norm_num),
    geneuclidUnitOfNat 13 55 (by norm_num), geneuclidUnitOfNat 13 30 (by norm_num),
    geneuclidUnitOfNat 13 5 (by norm_num), geneuclidUnitOfNat 13 110 (by norm_num),
    geneuclidUnitOfNat 13 7 (by norm_num), geneuclidUnitOfNat 13 385 (by norm_num),
    geneuclidUnitOfNat 13 35 (by norm_num), geneuclidUnitOfNat 13 231 (by norm_num),
    geneuclidUnitOfNat 13 11 (by norm_num), geneuclidUnitOfNat 13 77 (by norm_num)}

end MetaMathlibExt
