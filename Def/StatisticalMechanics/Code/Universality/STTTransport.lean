/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.STT.Part4
import Theorem.StatisticalMechanics.Code.Universality.STTTransport
open SimpleGraph


namespace StatMech

namespace Universality

variable {V : Type*}


def triCell (A B C : V) (ω : LocalConfig) : SimpleGraph V :=
  fromEdgeSet { e | (ω.1 ∧ e = s(B, C)) ∨ (ω.2.1 ∧ e = s(A, C)) ∨ (ω.2.2 ∧ e = s(A, B)) }


def starCell (A B C O : V) (ω : LocalConfig) : SimpleGraph V :=
  fromEdgeSet { e | (ω.1 ∧ e = s(O, A)) ∨ (ω.2.1 ∧ e = s(O, B)) ∨ (ω.2.2 ∧ e = s(O, C)) }


end Universality
end StatMech
