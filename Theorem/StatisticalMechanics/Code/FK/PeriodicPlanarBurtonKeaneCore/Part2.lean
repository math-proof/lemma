/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFiniteEnergy
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneCore.Part2
open MeasureTheory Set SimpleGraph
open scoped ENNReal


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [Countable V] [DecidableEq V]

theorem PeriodicGraph.infiniteClusters_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) :
    P.infiniteClusters (P.configTranslate z omega) =
      (fun C : Set V => P.shift z '' C) '' P.infiniteClusters omega := by
  ext C
  simp only [PeriodicGraph.infiniteClusters, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hinf, x, rfl⟩
    refine ⟨P.cluster omega (P.shift (-z) x), ⟨?_, _, rfl⟩, ?_⟩
    · exact (P.cluster_infinite_configTranslate z omega
        (P.shift (-z) x)).mp (by simpa using hinf)
    · simpa using (P.cluster_configTranslate z omega (P.shift (-z) x)).symm
  · rintro ⟨C, ⟨hinf, x, rfl⟩, rfl⟩
    exact ⟨(Set.infinite_image_iff
      (Set.injOn_of_injective (P.shift z).injective)).2 hinf,
      P.shift z x, (P.cluster_configTranslate z omega x).symm⟩

theorem PeriodicGraph.numInfiniteClusters_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) :
    P.numInfiniteClusters (P.configTranslate z omega) =
      P.numInfiniteClusters omega := by
  unfold PeriodicGraph.numInfiniteClusters
  rw [P.infiniteClusters_configTranslate]
  exact Set.InjOn.encard_image
    (Set.injOn_of_injective
      (Set.image_injective.mpr (P.shift z).injective))


end StatMech.FK.PeriodicPlanar
