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
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
public import Def.v1.Atlas.NumberTheoryI.code.KrasnerLemma
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
public import Def.v1.Atlas.NumberTheoryI.code.LocalGlobal.Part2
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
