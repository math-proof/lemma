/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
import Abbrev.v1.Atlas.NumberTheoryI.code.Adeles.Part3


noncomputable section

open NumberField IsDedekindDomain

open scoped TensorProduct

namespace NumberField.Adeles

variable {K : Type*} [Field K] [NumberField K]

section RestrictedProductDirectLimit

open Filter Set Topology

attribute [local instance] WithAbs.algebraLeft

@[reducible]
def embedAtPlace : (v : Place K) → K → placeCompletion v
  | .finite vi => algebraMap K (vi.adicCompletion K)
  | .infinite w => algebraMap K w.Completion

def diagonalAwayFrom (w : Place K) (x : K) : restrictedProductAwayFrom w :=
  RestrictedProduct.mk
    (fun (v : {v : Place K // v ≠ w}) => embedAtPlace v.val x)
    (by


     rw [Filter.eventually_cofinite]

     set f : {v : Place K // v ≠ w} → Option (HeightOneSpectrum (𝓞 K)) :=
       fun i => match i.val with
         | .finite vi => some vi
         | .infinite _ => none
     apply Set.Finite.of_injOn (f := f)
       (t := Option.some '' HeightOneSpectrum.Support (𝓞 K) x)
     ·
       intro ⟨v, hv⟩ hmem
       simp only [Set.mem_setOf_eq] at hmem
       cases v with
       | infinite _ => simp [placeIntegerSet] at hmem
       | finite vi =>
         simp only [f, Set.mem_image]
         refine ⟨vi, ?_, rfl⟩
         rw [HeightOneSpectrum.Support, Set.mem_setOf_eq]
         simp only [placeIntegerSet, SetLike.mem_coe, embedAtPlace] at hmem
         rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hmem
         have : algebraMap K (vi.adicCompletion K) x = (x : vi.adicCompletion K) := rfl
         rw [this] at hmem
         rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hmem
     ·
       intro ⟨v₁, hv₁⟩ hmem₁ ⟨v₂, hv₂⟩ hmem₂ hfeq
       simp only [Set.mem_setOf_eq] at hmem₁ hmem₂
       cases v₁ with
       | infinite _ => simp [placeIntegerSet] at hmem₁
       | finite vi₁ =>
         cases v₂ with
         | infinite _ => simp [placeIntegerSet] at hmem₂
         | finite vi₂ =>
           simp only [f] at hfeq
           have : vi₁ = vi₂ := Option.some_injective _ hfeq
           subst this; rfl
     ·
       exact (HeightOneSpectrum.Support.finite (𝓞 K) x).image _)

end RestrictedProductDirectLimit
end NumberField.Adeles
end
