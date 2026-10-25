/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.Algebra.Set.Closure.eq.N.of.Eq
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Invariant.Basic
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Lemma247
import Def.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part7


noncomputable section

open scoped Pointwise

open NumberField

namespace ArtinUnramified

attribute [instance] CyclicExtensionData.instGroupG
  CyclicExtensionData.instFiniteG CyclicExtensionData.instCyclicG
  CyclicExtensionData.instCommGroupM CyclicExtensionData.instFiniteM
  CyclicExtensionData.instAction

lemma _root_.Ideal.spanNorm_mem_nonZeroDivisors
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {I : Ideal (𝓞 L)} (hI : I ∈ nonZeroDivisors (Ideal (𝓞 L))) :
    Ideal.spanNorm (𝓞 K) I ∈ nonZeroDivisors (Ideal (𝓞 K)) := by
  rw [mem_nonZeroDivisors_iff_ne_zero] at hI ⊢
  intro h; apply hI
  rwa [show (0 : Ideal (𝓞 K)) = ⊥ from rfl, Ideal.spanNorm_eq_bot_iff,
       show (⊥ : Ideal (𝓞 L)) = 0 from rfl] at h

end ArtinUnramified
end
