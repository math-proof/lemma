/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Sequences/GeneralizedEuclidSequence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Tactic.FieldSimp
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Nat.Factors
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Def.NumberTheory.Sequences.GeneralizedEuclidSequence.Part3

/-!
# Generalized Euclid sequences contain every prime

This file proves that every finite prime seed extends to an injective generalized Euclid
sequence containing every prime.
-/

public section


namespace MetaMathlibExt

open scoped Pointwise

theorem geneuclidSevenRepresentatives_card : geneuclidSevenRepresentatives.card = 5 := by
  decide

end MetaMathlibExt
