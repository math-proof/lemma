/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part2
open Finset SimpleGraph

set_option maxHeartbeats 800000


namespace StatMech.FrontierD

noncomputable section

open StatMech

section FiniteBoolPushforward

variable {E : Type*} [Fintype E] [DecidableEq E]

def finiteBoolEventMass
    (mu : ConfigSpace E → Real) (A : Set (ConfigSpace E)) : Real :=
  ∑ omega : ConfigSpace E, A.indicator mu omega

def finiteBoolForceClosed (I : Finset E)
    (omega : ConfigSpace E) : ConfigSpace E :=
  fun e => if e ∈ I then false else omega e

def finiteBoolForceOpen (I : Finset E)
    (omega : ConfigSpace E) : ConfigSpace E :=
  fun e => if e ∈ I then true else omega e

end FiniteBoolPushforward
end
end StatMech.FrontierD
