/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Theorem.Set.Closure.eq.N.of.Eq
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.Invariant.Basic
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Lemma247
public import Theorem.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part5

@[expose] public section

noncomputable section

open scoped Pointwise

open NumberField

namespace ArtinUnramified

attribute [instance] CyclicExtensionData.instGroupG
  CyclicExtensionData.instFiniteG CyclicExtensionData.instCyclicG
  CyclicExtensionData.instCommGroupM CyclicExtensionData.instFiniteM
  CyclicExtensionData.instAction

def spanNormNZD (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    (nonZeroDivisors (Ideal (𝓞 L))) →* (nonZeroDivisors (Ideal (𝓞 K))) where
  toFun I := ⟨Ideal.spanNorm (𝓞 K) I.1, Ideal.spanNorm_mem_nonZeroDivisors I.2⟩
  map_one' := by ext; simp
  map_mul' := fun I J => by ext; simp

def normToClK (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    (nonZeroDivisors (Ideal (𝓞 L))) →* ClassGroup (𝓞 K) :=
  ClassGroup.mk0.comp (spanNormNZD K L)

end ArtinUnramified
end
