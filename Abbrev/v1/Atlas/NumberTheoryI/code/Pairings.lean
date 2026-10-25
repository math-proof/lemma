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
import Def.v1.Atlas.NumberTheoryI.code.Pairings
open Submodule LinearMap


noncomputable section

abbrev IsPerfectSelfPairing (A : Type*) [CommRing A] (M : Type*)
    [AddCommGroup M] [Module A M] (p : M →ₗ[A] M →ₗ[A] A) : Prop :=
  p.IsPerfPair

end
