/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc5_minimalwitnessencoded
open Finset


namespace StatMech.Walls

open StatMech ConfigSpace

variable {E : Type*}

section Fintype

variable [Fintype E] [DecidableEq E]

variable {A B : Set (ConfigSpace E)} {ω : ConfigSpace E}


theorem occursMinimalWitness_support_unique {s s' K K' L L' : Finset E}
    (h : OccursMinimalWitness A B ω s K L) (h' : OccursMinimalWitness A B ω s' K' L') :
    s = s' := by
  rw [h.support, h'.support]


theorem occursMinimalWitness_decode {s K L : Finset E}
    (h : OccursMinimalWitness A B ω s K L) :
    supportCfg s = ω :=
  supportCfg_of_occursMinimalWitness h


end Fintype
end StatMech.Walls
