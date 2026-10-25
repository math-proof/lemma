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
import Theorem.v1.Atlas.NumberTheoryI.code.PairingsTheorems
open Submodule LinearMap Module


noncomputable section

section DirectSumDualLattice

structure IsLocALattice
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (V : Type*) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    (S : Submonoid A) (N : Submodule A V) : Prop where
  fg_loc : ∃ T : Finset V, N = (Submodule.span A (T : Set V)).localize S
  span_eq_top : Submodule.span K (N : Set V) = ⊤

end DirectSumDualLattice
end
