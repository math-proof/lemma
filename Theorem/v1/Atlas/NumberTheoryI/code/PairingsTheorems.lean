/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.Pairings.Part2
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.Lattice
import Def.v1.Atlas.NumberTheoryI.code.PairingsTheorems
open Submodule LinearMap Module


noncomputable section

section Connection

variable
  {A : Type*} [CommRing A] [IsDomain A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

omit [IsDomain A] [IsFractionRing A K] in
theorem dualSubmodule_antitone (B : V →ₗ[K] V →ₗ[K] K) :
    Antitone (BilinForm.dualSubmodule B : Submodule A V → Submodule A V) := by
  intro N₁ N₂ h x hx y hy
  exact hx y (h hy)

variable {ι : Type*} [DecidableEq ι] [Finite ι]

theorem thm_5_12_injective (B : V →ₗ[K] V →ₗ[K] K) (hB : B.Nondegenerate)
    (N : Submodule A V) (hN : span K (N : Set V) = ⊤) :
    Function.Injective (BilinForm.dualSubmoduleToDual B N) :=
  BilinForm.dualSubmoduleToDual_injective B hB N hN

end Connection
end
