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
import Theorem.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part6


noncomputable section

open scoped Pointwise

open NumberField

namespace ArtinUnramified

attribute [instance] CyclicExtensionData.instGroupG
  CyclicExtensionData.instFiniteG CyclicExtensionData.instCyclicG
  CyclicExtensionData.instCommGroupM CyclicExtensionData.instFiniteM
  CyclicExtensionData.instAction

open FractionalIdeal in
def normOnFracUnits (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    (FractionalIdeal (nonZeroDivisors (𝓞 L)) (FractionRing (𝓞 L)))ˣ →*
      ClassGroup (𝓞 K) where
  toFun I := normToClK K L ⟨ClassGroup.integralRep (I : FractionalIdeal _ _),
    ClassGroup.integralRep_mem_nonZeroDivisors I.ne_zero⟩
  map_one' :=
    normToClK_of_mk0_eq_one (by rw [ClassGroup.mk0_integralRep, map_one])
  map_mul' := fun I J => by
    have hmul : ClassGroup.mk0 (R := 𝓞 L) ⟨ClassGroup.integralRep ((I * J : _) : _),
        ClassGroup.integralRep_mem_nonZeroDivisors (I * J).ne_zero⟩ =
      ClassGroup.mk0 (⟨ClassGroup.integralRep (I : _),
        ClassGroup.integralRep_mem_nonZeroDivisors I.ne_zero⟩ *
       ⟨ClassGroup.integralRep (J : _),
        ClassGroup.integralRep_mem_nonZeroDivisors J.ne_zero⟩) := by
      rw [ClassGroup.mk0_integralRep, map_mul (ClassGroup.mk (R := 𝓞 L)),
          ← ClassGroup.mk0_integralRep I, ← ClassGroup.mk0_integralRep J, map_mul]
    show normToClK K L ⟨ClassGroup.integralRep ((I * J : _) : _), _⟩ =
      normToClK K L ⟨ClassGroup.integralRep (I : _), _⟩ *
      normToClK K L ⟨ClassGroup.integralRep (J : _), _⟩
    rw [normToClK_well_defined hmul, map_mul]

end ArtinUnramified
end
