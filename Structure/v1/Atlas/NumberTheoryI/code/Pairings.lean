/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Pairings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Module
import Abbrev.v1.Atlas.NumberTheoryI.code.Pairings
open Submodule LinearMap


noncomputable section

structure IsALattice
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (V : Type*) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    (M : Submodule A V) : Prop where
  fg : M.FG
  span_eq_top : Submodule.span K (M : Set V) = ⊤

end
