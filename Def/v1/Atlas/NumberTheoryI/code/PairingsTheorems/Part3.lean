/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.NumberTheoryI.code.Pairings.Part2
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Lattice
public import Theorem.v1.Atlas.NumberTheoryI.code.PairingsTheorems.Part2

@[expose] public section

open Submodule LinearMap Module


noncomputable section

section DirectSumDualLattice

def thm_5_12_linearEquiv
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (hB : B.Nondegenerate)
    (M : Submodule A V) (hM : IsALattice A K V M) :
    ↥(BilinForm.dualSubmodule B M) ≃ₗ[A] Module.Dual A ↥M :=
  LinearEquiv.ofBijective (BilinForm.dualSubmoduleToDual B M) (thm_5_12 B hB M hM).2

end DirectSumDualLattice
end
