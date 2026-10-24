/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IdealNorm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

namespace IdealNorm

variable {𝒪 : Type*} [CommRing 𝒪]

/-- The (absolute) norm of an ideal `𝔞` of `𝒪`, defined as the cardinality of the
quotient `𝒪 / 𝔞`. -/
noncomputable def idealNorm (𝔞 : Ideal 𝒪) : ℕ := Submodule.cardQuot 𝔞
