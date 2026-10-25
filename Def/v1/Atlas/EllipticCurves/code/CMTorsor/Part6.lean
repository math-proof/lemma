/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.ClassGroup
import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part6
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic
import Instance.v1.Atlas.EllipticCurves.code.CMTorsor.Part3


namespace IdealClassGroup

open nonZeroDivisors FractionalIdeal

section ImaginaryQuadratic

open ProperIdealInvertible

variable {d : ℤ}

/-- Identification of the quotient
`InvertibleFractionalIdeals(ℤ√d) / PrincipalFractionalIdeals(ℤ√d)` with the class group
`Cl(ℤ√d)` (in the imaginary quadratic case). -/
noncomputable def classGroupQuotient_imaginaryQuadratic
    [IsDomain (ℤ√d)]
    (K : Type*) [Field K] [Algebra (ℤ√d) K] [IsFractionRing (ℤ√d) K] :
    (FractionalIdeal (ℤ√d)⁰ K)ˣ ⧸ (toPrincipalIdeal (ℤ√d) K).range ≃*
    ClassGroup (ℤ√d) :=
  classGroup_mulEquiv (ℤ√d) K

end ImaginaryQuadratic

section ClassGroupQuotientEquiv

open ComplexLattice

variable (𝒪 : Subring ℂ) [IsDomain 𝒪]

/-- Specialised version for `𝒪 = ℤ√d`: the quotient
`(FractionalIdeal (ℤ√d) K)ˣ / Principal` is `Cl(ℤ√d)`. -/
noncomputable def classGroupQuotient_Zsqrtd (d : ℤ) [IsDomain (ℤ√d)]
    (K : Type*) [Field K] [Algebra (ℤ√d) K] [IsFractionRing (ℤ√d) K] :
    (FractionalIdeal (ℤ√d)⁰ K)ˣ ⧸ (toPrincipalIdeal (ℤ√d) K).range ≃*
    ClassGroup (ℤ√d) :=
  classGroup_mulEquiv (ℤ√d) K

end ClassGroupQuotientEquiv

end IdealClassGroup

namespace IdealTorsion

variable {𝒪 : Type*} [CommRing 𝒪]

variable {E : Type*} [AddCommGroup E] [Module 𝒪 E]

/-- The `𝔞`-torsion submodule of an `𝒪`-module `E`: the set of `P ∈ E` such that
`α · P = 0` for every `α ∈ 𝔞`. -/
def idealTorsion (𝔞 : Ideal 𝒪) : Submodule 𝒪 E where
  carrier := {P : E | ∀ α ∈ 𝔞, α • P = 0}
  zero_mem' := fun α _ => smul_zero α
  add_mem' := fun {P Q} hP hQ α hα => by rw [smul_add, hP α hα, hQ α hα, add_zero]
  smul_mem' := fun r {P} hP α hα => by
    rw [smul_comm]
    exact smul_eq_zero_of_right r (hP α hα)

/-- The `𝔞`-torsion submodule viewed as an additive subgroup of `E`. -/
def idealTorsionAddSubgroup (𝔞 : Ideal 𝒪) : AddSubgroup E :=
  (idealTorsion 𝔞).toAddSubgroup

end IdealTorsion
