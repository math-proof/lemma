/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma5.Part3


namespace StatMech.Onsager

open Matrix BigOperators


def ons_revSeg {E} {n : ℕ} [NeZero n] (rev : E → E) (l m : Fin n) (v : Fin n → E) :
    Fin n → E :=
  fun k => if l ≤ k ∧ k ≤ m then rev (v (ons_mir l m k)) else v k


end StatMech.Onsager
