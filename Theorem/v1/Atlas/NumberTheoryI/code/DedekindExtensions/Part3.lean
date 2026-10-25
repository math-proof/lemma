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
import Def.v1.Atlas.NumberTheoryI.code.DedekindExtensions.Part3
open Module


noncomputable section

section DualInvertibleFractionalIdeal

open scoped nonZeroDivisors

variable (A : Type*) [CommRing A] [IsDomain A]

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

theorem colonSubmodule_eq_coe_inv (M : FractionalIdeal A⁰ K) (hM : M ≠ 0) :
    colonSubmodule A K (↑M : Submodule A K) = (↑(M⁻¹) : Submodule A K) := by
  ext x
  simp only [colonSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk]
  constructor
  · intro hx
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_inv_iff hM]
    intro y hy
    rw [FractionalIdeal.mem_one_iff]
    exact hx y (FractionalIdeal.mem_coe.mp hy)
  · intro hx m hm
    have hx' := FractionalIdeal.mem_coe.mp hx
    rw [FractionalIdeal.mem_inv_iff hM] at hx'
    have := hx' m (FractionalIdeal.mem_coe.mpr hm)
    rw [FractionalIdeal.mem_one_iff] at this
    exact this

end DualInvertibleFractionalIdeal
end
