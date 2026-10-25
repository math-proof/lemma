/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.STT.Part4
import Theorem.StatisticalMechanics.Code.Universality.STTTransport.Part2
open SimpleGraph


namespace StatMech

namespace Universality

variable {V : Type*}


variable (E : SimpleGraph V) {A B C : V}


def MatchesPattern (ωt ωs : LocalConfig) : Prop :=
  triAB ωt = starAB ωs ∧ triAC ωt = starAC ωs ∧ triBC ωt = starBC ωs


end Universality
end StatMech
