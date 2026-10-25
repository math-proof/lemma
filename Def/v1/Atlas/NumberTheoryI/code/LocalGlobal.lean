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
open scoped NumberField TensorProduct
open NumberField IsDedekindDomain


noncomputable section

def algEquivOfFinrankOne (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (h : Module.finrank F E = 1) : E ≃ₐ[F] F := by
  have htop := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hsurj : Function.Surjective (algebraMap F E) := fun x => by
    have : x ∈ (⊤ : Subalgebra F E) := Algebra.mem_top; rwa [← htop] at this
  exact (AlgEquiv.ofBijective (Algebra.ofId F E) ⟨(algebraMap F E).injective, hsurj⟩).symm

end
