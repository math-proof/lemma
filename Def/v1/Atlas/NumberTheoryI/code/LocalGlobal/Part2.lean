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
public import Theorem.v1.Atlas.NumberTheoryI.code.LocalGlobal
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

def galoisGroupMulEquivTrivial (K F E : Type*) [Field K] [Field F] [Field E]
    [Algebra F E] [FiniteDimensional F E] (h : Module.finrank F E = 1) :
    MulEquiv (K ≃ₐ[K] K) (E ≃ₐ[F] E) where
  toFun _ := AlgEquiv.refl
  invFun _ := AlgEquiv.refl
  left_inv e := by ext x; exact (AlgEquiv.commutes e x).symm
  right_inv e := (algEquiv_eq_refl_of_finrank_one h e).symm
  map_mul' _ _ := by symm; exact algEquiv_eq_refl_of_finrank_one h _

noncomputable def commKvAlgEquiv (v : HeightOneSpectrum (𝓞 K)) :
    letI := @Algebra.TensorProduct.rightAlgebra K L (v.adicCompletion K) _ _ _ _ _
    v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K] (L ⊗[K] v.adicCompletion K) := by
  letI := @Algebra.TensorProduct.rightAlgebra K L (v.adicCompletion K) _ _ _ _ _
  exact @AlgEquiv.ofRingEquiv (v.adicCompletion K)
    (v.adicCompletion K ⊗[K] L) (L ⊗[K] v.adicCompletion K) _ _ _
    inferInstance
    Algebra.TensorProduct.rightAlgebra
    (f := (Algebra.TensorProduct.comm K (v.adicCompletion K) L).toRingEquiv)
    (fun r => by
      simp [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.algebraMap_apply,
            Algebra.TensorProduct.right_algebraMap_apply])

end
