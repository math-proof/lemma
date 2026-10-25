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
