/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindExtensions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.NumberTheory.NumberField.Basic
import Def.v1.Atlas.NumberTheoryI.code.Pairings.Part2
open Module


noncomputable section

section DualModule

variable {A : Type*} [CommRing A]

variable {M N P : Type*} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]

def dualDirectSumEquiv :
    Module.Dual A (M × N) ≃ₗ[A] Module.Dual A M × Module.Dual A N :=
  (Module.dualProdDualEquivDual A M N).symm

end DualDirectSum


section DualColonSubmodule

variable (A : Type*) [CommRing A] [IsDomain A]

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

def colonSubmodule (M : Submodule A K) : Submodule A K where
  carrier := {x : K | ∀ m : K, m ∈ M → x * m ∈ (algebraMap A K).range}
  add_mem' := by
    intro x y hx hy m hm; rw [add_mul]
    exact (algebraMap A K).range.add_mem (hx m hm) (hy m hm)
  zero_mem' := by intro m _; rw [zero_mul]; exact (algebraMap A K).range.zero_mem
  smul_mem' := by
    intro c x hx m hm; rw [Algebra.smul_def, mul_assoc]
    exact (algebraMap A K).range.mul_mem ⟨c, rfl⟩ (hx m hm)


noncomputable def colonToA (M : Submodule A K) (x : colonSubmodule A K M) (m : M) : A :=
  (x.2 (m : K) m.2).choose

end DualColonSubmodule
end
