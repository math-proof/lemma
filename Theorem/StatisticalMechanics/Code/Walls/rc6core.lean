/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc6deficitform.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc6relabelinvariance.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc6eventdowncompression
import Theorem.StatisticalMechanics.Code.Walls.rc6blmonovariant
import Theorem.StatisticalMechanics.Code.Walls.rc6hallavailable.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc6canonicalwitness.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc6overlapsplit
import Theorem.StatisticalMechanics.Code.Walls.rc6localmirror.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc5_core.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer2000Close.Part5
import Def.StatisticalMechanics.Code.Walls.rc6core
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


section CanonMirror

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in


theorem rc6_canonMirror_mem (A B : Set (ConfigSpace α)) {ω : ConfigSpace α}
    (hω : ω ∈ disjointOccurrence A B) :
    rc6_canonMirror A B ω ∈ A ∩ rmr_reflect B := by
  obtain ⟨hA, hB, hKL⟩ := canonicalWitness_occursOn hω
  exact rc6_mirrorL_mem (Finset.disjoint_coe.mpr hKL) hA hB

open Classical in


theorem rc6_canonMirror_mapsTo (A B : Set (ConfigSpace α)) :
    Set.MapsTo (rc6_canonMirror A B) (disjointOccurrence A B) (A ∩ rmr_reflect B) :=
  fun _ hω => rc6_canonMirror_mem A B hω


theorem rc6_boxReflectInjection_of_canonMirror_injOn (A B : Set (ConfigSpace α))
    (hinj : Set.InjOn (rc6_canonMirror A B) {ω | ω ∈ disjointOccurrence A B}) :
    rc5_BoxReflectInjection A B :=
  ⟨rc6_canonMirror A B, hinj, fun _ hω => rc6_canonMirror_mem A B hω⟩

end CanonMirror
end StatMech.Walls
