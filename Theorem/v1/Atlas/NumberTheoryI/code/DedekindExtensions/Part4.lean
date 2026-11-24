module
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.Ideal.IntegralClosure
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.NumberTheory.NumberField.Basic
public import Def.v1.Atlas.NumberTheoryI.code.Pairings.Part2
public import Def.v1.Atlas.NumberTheoryI.code.DedekindExtensions.Part4
open Module


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindExtensions.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

section DualLattice

example (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (V : Type*) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    (φ : V →ₗ[K] V →ₗ[K] K) (M : Submodule A V) :
    dualLattice A K V φ M = dualLattice A K V φ M := rfl

end DualLattice
end
