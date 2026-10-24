/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TracePairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Transitivity

open Algebra

section TracePairingDef

variable (A : Type*) [CommRing A]
variable (B : Type*) [CommRing B] [Algebra A B]

noncomputable def tracePairing : LinearMap.BilinForm A B :=
  Algebra.traceForm A B

end TracePairingDef

section AKLB

variable (A : Type*) [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
variable [Algebra A L] [IsScalarTower A K L]
variable (B : Type*) [CommRing B] [IsDomain B] [Algebra B L] [IsIntegralClosure B A L]
  [Algebra A B] [IsScalarTower A B L]
