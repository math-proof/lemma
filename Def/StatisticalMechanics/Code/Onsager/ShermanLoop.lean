/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLoop.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.TracePowWalk


namespace StatMech.Onsager

open Matrix BigOperators


noncomputable def ons_loopWeight {E : Type*} [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    {n : ℕ} [NeZero n] (v : Fin n → E) : ℂ := ∏ k : Fin n, Λ (v k) (v (k + 1))


def ons_cyclicShift {E : Type*} {n : ℕ} [NeZero n] (v : Fin n → E) : Fin n → E :=
  fun k => v (k + 1)


end StatMech.Onsager
