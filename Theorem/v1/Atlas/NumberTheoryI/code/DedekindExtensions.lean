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
import Def.v1.Atlas.NumberTheoryI.code.DedekindExtensions
open Module


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
