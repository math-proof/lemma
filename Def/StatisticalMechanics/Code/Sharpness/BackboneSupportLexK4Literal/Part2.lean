/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Literal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Literal
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

def shbParitySupportOn {E : Type*} [DecidableEq E]
    (S : Finset E) (m : ↑S → ℕ) : Finset E :=
  (S.attach.filter fun e => Odd (m e)).map
    ⟨Subtype.val, Subtype.val_injective⟩

end StatMech.Sharpness
