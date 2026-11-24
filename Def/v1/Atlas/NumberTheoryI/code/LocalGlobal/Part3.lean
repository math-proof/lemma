module
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Abbrev.v1.Atlas.NumberTheoryI.code.GlobalFields
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.GlobalFields
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.KrasnerLemma
public import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
public import Def.v1.Atlas.NumberTheoryI.code.KrasnerLemma
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
public import Theorem.v1.Atlas.NumberTheoryI.code.LocalGlobal.Part2
open scoped NumberField TensorProduct
open NumberField IsDedekindDomain


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

def finSuccLinearEquiv' (R : Type*) [CommRing R] {n : ℕ} (A : Fin (n + 1) → Type*)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] :
    (∀ i : Fin (n + 1), A i) ≃ₗ[R] A 0 × (∀ i : Fin n, A (Fin.succ i)) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by ext i; exact congr_fun (Fin.cons_self_tail f) i
  right_inv p := by
    ext
    · exact Fin.cons_zero p.1 p.2
    · exact Fin.cons_succ p.1 p.2 _
  map_add' f g := by ext <;> rfl
  map_smul' r f := by ext <;> rfl

end
