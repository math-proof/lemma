/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part4


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def horizontalFirstHitBelowReflect
    (t : Nat) (start level : Int) :
    HorizontalFirstHitBelow t start level →
      HorizontalFirstHitBelow t (2 * level - start) level := fun z =>
  ⟨z.1.reflectPrefix,
    reflectPrefix_firstHit z.1 z.2.1,
    reflectPrefix_valid z.1 z.2.2.1,
    (reflectPrefix_length z.1).trans z.2.2.2.1,
    (reflectPrefix_endpoint_fst z.1).symm ▸ z.2.2.2.2.1,
    by
      intro d hd
      change d ∈ z.1.before.map reflectIncrement ++
        z.1.after at hd
      rcases List.mem_append.mp hd with hd | hd
      · rcases List.mem_map.mp hd with ⟨e, he, rfl⟩
        simpa [reflectIncrement] using z.2.2.2.2.2 e
          (List.mem_append.mpr (Or.inl he))
      · exact z.2.2.2.2.2 d (List.mem_append.mpr (Or.inr hd))⟩

end
end StatMech.Universality
