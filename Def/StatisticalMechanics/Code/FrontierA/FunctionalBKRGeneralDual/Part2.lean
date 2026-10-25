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
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.ConfigSpace

open StatMech.Walls

open StatMech.Walls.Reimer

variable {E : Type*} [Fintype E] [DecidableEq E]

def KSSWeightInjection (A B : Set (ConfigSpace E)) : Prop :=
  ∃ Phi : ConfigSpace E × ConfigSpace E → ConfigSpace E × ConfigSpace E,
    (∀ p, p ∈ dualDisjointOccurrence A B → (Phi p).1 ∈ A ∩ B) ∧
    (∀ (phi : E → Bool → ℝ) p, p ∈ dualDisjointOccurrence A B →
      pweight phi (Phi p).1 * pweight phi (Phi p).2 =
        pweight phi p.1 * pweight phi p.2) ∧
    Set.InjOn Phi (dualDisjointOccurrence A B)


end StatMech.FrontierA
