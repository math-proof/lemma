/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Abbrev.v1.Atlas.NumberTheoryI.code.GlobalFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.GlobalFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KrasnerLemma
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
import Def.v1.Atlas.NumberTheoryI.code.KrasnerLemma
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.SpecificDegree
import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
import Theorem.v1.Atlas.NumberTheoryI.code.LocalGlobal.Part2
open scoped NumberField TensorProduct
open NumberField IsDedekindDomain


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
