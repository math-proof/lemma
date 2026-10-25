/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_minimalwitnessencoded.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc2_minimalwitness
open Finset


namespace StatMech.Walls

open StatMech ConfigSpace

variable {E : Type*}

section Fintype

variable [Fintype E] [DecidableEq E]

variable {A B : Set (ConfigSpace E)} {ω : ConfigSpace E}


structure SupportEncodedMinimalWitness (A B : Set (ConfigSpace E)) (ω : ConfigSpace E)
    (s K L : Finset E) : Prop where
  
  support : s = cfgSupport ω
  
  disjoint : Disjoint K L
  
  minimalA : Minimal (fun S => cylinder S ω ⊆ A) K
  
  minimalB : Minimal (fun S => cylinder S ω ⊆ B) L


end Fintype
end StatMech.Walls
