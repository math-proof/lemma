/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisWord.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForwardSubdivision
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordPhaseGlue.Part2
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisSubdivision.Part5


namespace StatMech.FrontierA

open Set

open scoped BigOperators

open StatMech.Onsager.BaseCase


theorem kwPrefixPositions_flatten_map
    (start : ℕ → ℤ × ℤ) (blocks : List (List (Fin 4)))
    (hstep : ∀ k (hk : k < blocks.length),
      (((blocks[k]'hk).map stepOf).sum) = start (k + 1) - start k) :
    (kwPrefixPositions blocks.flatten).map (start 0 + ·) =
      kwIndexedPrefixBlocks start blocks := by
  induction blocks generalizing start with
  | nil => simp [kwIndexedPrefixBlocks]
  | cons word tail ih =>
      have hzero : (word.map stepOf).sum = start 1 - start 0 := by
        simpa using hstep 0 (by simp)
      have htail : ∀ k (hk : k < tail.length),
          (((tail[k]'hk).map stepOf).sum) =
            start (k + 1 + 1) - start (k + 1) := by
        intro k hk
        simpa [Nat.add_assoc] using hstep (k + 1) (by simpa using hk)
      have hi := ih (fun k ↦ start (k + 1)) htail
      rw [List.flatten_cons, kwPrefixPositions_append, List.map_append]
      simp only [kwIndexedPrefixBlocks, List.mapIdx_cons,
        List.flatten_cons]
      congr 1
      rw [List.map_map]
      calc
        (kwPrefixPositions tail.flatten).map
              ((start 0 + ·) ∘ ((word.map stepOf).sum + ·)) =
            (kwPrefixPositions tail.flatten).map (start 1 + ·) := by
          apply List.map_congr_left
          intro q hq
          simp only [Function.comp_apply]
          rw [hzero]
          abel
        _ = (tail.mapIdx fun k word ↦
              (kwPrefixPositions word).map (start (k + 1) + ·)).flatten := by
          simpa [kwIndexedPrefixBlocks] using hi


end StatMech.FrontierA
