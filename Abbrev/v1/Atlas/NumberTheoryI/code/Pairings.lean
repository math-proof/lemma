/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Pairings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Module
public import Def.v1.Atlas.NumberTheoryI.code.Pairings
open Submodule LinearMap


@[expose] public noncomputable section

abbrev IsPerfectSelfPairing (A : Type*) [CommRing A] (M : Type*)
    [AddCommGroup M] [Module A M] (p : M →ₗ[A] M →ₗ[A] A) : Prop :=
  p.IsPerfPair

end
