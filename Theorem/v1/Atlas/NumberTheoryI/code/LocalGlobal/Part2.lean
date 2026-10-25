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
import Def.v1.Atlas.NumberTheoryI.code.LocalGlobal.Part2
open scoped NumberField TensorProduct
open NumberField IsDedekindDomain


noncomputable section

lemma norm_baseChange_eq
    (v : HeightOneSpectrum (𝓞 K))
    (α : L) :
    algebraMap K (v.adicCompletion K) (Algebra.norm K α) =
    @Algebra.norm (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _ _
      Algebra.TensorProduct.rightAlgebra
      (α ⊗ₜ[K] (1 : v.adicCompletion K)) := by
  rw [Algebra.norm_apply K α, ← LinearMap.det_baseChange (Algebra.lmul K L α),
      Algebra.baseChange_lmul, ← Algebra.norm_apply (v.adicCompletion K)
        ((1 : v.adicCompletion K) ⊗ₜ[K] α)]
  have h : commKvAlgEquiv v ((1 : v.adicCompletion K) ⊗ₜ[K] α) =
      (α ⊗ₜ[K] (1 : v.adicCompletion K)) := by
    simp [commKvAlgEquiv, AlgEquiv.ofRingEquiv, Algebra.TensorProduct.comm_tmul]
  rw [← h]
  exact (@Algebra.norm_eq_of_algEquiv (v.adicCompletion K)
    (v.adicCompletion K ⊗[K] L) (L ⊗[K] v.adicCompletion K) _ _ _
    _ Algebra.TensorProduct.rightAlgebra (commKvAlgEquiv v)
    ((1 : v.adicCompletion K) ⊗ₜ[K] α)).symm

lemma trace_baseChange_eq
    (v : HeightOneSpectrum (𝓞 K))
    (α : L) :
    algebraMap K (v.adicCompletion K) (Algebra.trace K L α) =
    @Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _ _
      Algebra.TensorProduct.rightAlgebra
      (α ⊗ₜ[K] (1 : v.adicCompletion K)) := by
  rw [Algebra.trace_apply K α,
      ← LinearMap.trace_baseChange (Algebra.lmul K L α) (v.adicCompletion K),
      Algebra.baseChange_lmul,
      ← Algebra.trace_apply (v.adicCompletion K) ((1 : v.adicCompletion K) ⊗ₜ[K] α)]
  have h : commKvAlgEquiv v ((1 : v.adicCompletion K) ⊗ₜ[K] α) =
      (α ⊗ₜ[K] (1 : v.adicCompletion K)) := by
    simp [commKvAlgEquiv, AlgEquiv.ofRingEquiv, Algebra.TensorProduct.comm_tmul]
  rw [← h]
  exact (@Algebra.trace_eq_of_algEquiv (v.adicCompletion K)
    (v.adicCompletion K ⊗[K] L) (L ⊗[K] v.adicCompletion K) _ _ _
    _ Algebra.TensorProduct.rightAlgebra (commKvAlgEquiv v)
    ((1 : v.adicCompletion K) ⊗ₜ[K] α)).symm

end
