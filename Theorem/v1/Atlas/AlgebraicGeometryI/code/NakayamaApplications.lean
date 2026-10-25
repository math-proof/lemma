/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NakayamaApplications.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Jacobson.Ring
set_option maxHeartbeats 800000


noncomputable section

open Ideal

section Nakayama

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

end Nakayama
end
