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
import Def.v1.Atlas.NumberTheoryI.code.DedekindExtensions.Part4
open Module


noncomputable section

section DualLattice

example (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (V : Type*) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    (φ : V →ₗ[K] V →ₗ[K] K) (M : Submodule A V) :
    dualLattice A K V φ M = dualLattice A K V φ M := rfl

end DualLattice
end
