/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurveGenusGeometric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 400000

noncomputable section

namespace CurveGenusGeometric

variable (k : Type*) [Field k]
variable (A : Type*) [CommRing A] [Algebra k A]

/-- The geometric genus `g_m` of a curve over `k`, defined as the `k`-dimension of the global
sections of the canonical sheaf, modeled here as `Ω[A⁄k]`. -/
def geometricGenus : ℕ :=
  Module.finrank k (Ω[A⁄k])

/-- The arithmetic genus of a curve, defined as the `k`-dimension of `H¹(O_X)`. -/
def arithmeticGenus (H1_O : Type*) [AddCommGroup H1_O] [Module k H1_O] : ℕ :=
  Module.finrank k H1_O
