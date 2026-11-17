/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindExtensions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
public import Def.v1.Atlas.NumberTheoryI.code.DedekindExtensions
open Module

public section

noncomputable section

section DualColonSubmodule

variable (A : Type*) [CommRing A] [IsDomain A]

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

omit [IsDomain A] [IsFractionRing A K] in
theorem colonToA_spec (M : Submodule A K) (x : colonSubmodule A K M) (m : M) :
    algebraMap A K (colonToA A K M x m) = (x : K) * (m : K) :=
  (x.2 (m : K) m.2).choose_spec

end DualColonSubmodule
end
