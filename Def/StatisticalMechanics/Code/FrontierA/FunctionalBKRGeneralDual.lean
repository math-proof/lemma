/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneDual.Part3
import Theorem.StatisticalMechanics.Code.Walls.rb3reimerclose.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc4_core
import Theorem.StatisticalMechanics.Code.Walls.rc3_keyflipinvolutive
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.ConfigSpace

open StatMech.Walls

open StatMech.Walls.Reimer

variable {E : Type*} [Fintype E] [DecidableEq E]

def kssTwist (k : ConfigSpace E × ConfigSpace E)
    (B : Set (ConfigSpace E)) : Set (ConfigSpace E) :=
  {omega | poc_keyFlip k omega ∈ B}

open Classical in

noncomputable def kssDualOrbit (A B : Set (ConfigSpace E))
    (k : ConfigSpace E × ConfigSpace E) :
    Finset (ConfigSpace E × ConfigSpace E) :=
  Finset.univ.filter fun p =>
    p ∈ dualDisjointOccurrence A B ∧ orbitKey p = k

open Classical in

noncomputable def kssDiagonalOrbit (A B : Set (ConfigSpace E))
    (k : ConfigSpace E × ConfigSpace E) :
    Finset (ConfigSpace E × ConfigSpace E) :=
  Finset.univ.filter fun p => p.1 ∈ A ∩ B ∧ orbitKey p = k

end StatMech.FrontierA
