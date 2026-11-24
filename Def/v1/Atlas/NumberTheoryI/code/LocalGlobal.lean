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

def algEquivOfFinrankOne (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (h : Module.finrank F E = 1) : E ≃ₐ[F] F := by
  have htop := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hsurj : Function.Surjective (algebraMap F E) := fun x => by
    have : x ∈ (⊤ : Subalgebra F E) := Algebra.mem_top; rwa [← htop] at this
  exact (AlgEquiv.ofBijective (Algebra.ofId F E) ⟨(algebraMap F E).injective, hsurj⟩).symm

end
