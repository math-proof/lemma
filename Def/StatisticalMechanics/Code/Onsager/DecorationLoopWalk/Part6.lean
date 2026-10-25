/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part4
import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part6


namespace StatMech.Onsager

open Finset SimpleGraph

noncomputable def ons_decLoopWalk
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    (ons_decGraph L).Walk (d 0) (d 0) := by
  let states := List.ofFn (ons_decGeometricLoopStates d)
  have hstatesNonempty : states ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_ofFn]
    exact NeZero.pos n
  have hhead : states.head? = some (d 0) := by
    rw [List.head?_eq_head hstatesNonempty,
      List.head_ofFn hstatesNonempty]
    simp [ons_decGeometricLoopStates]
  have hstates : states = d 0 :: states.tail := by
    apply List.eq_cons_of_mem_head?
    simpa [hhead]
  have hchain : List.IsChain (ons_decGeometricStep L)
      (states ++ [d 0]) := by
    simpa [states, ons_decGeometricLoopStates] using
      ons_isChain_closed_ofFn_mk (ons_decGeometricLoopStates d)
        (ons_decGeometricLoopStates_valid d hvalid)
  have hchain' : List.IsChain (ons_decGeometricStep L)
      (d 0 :: (states.tail ++ [d 0])) := by
    rw [← List.cons_append, ← hstates]
    exact hchain
  let walk := ons_decWalkOfKWChain L (d 0)
    (states.tail ++ [d 0]) hchain'
  exact walk.copy rfl (ons_decKWChainLast_append_singleton _ _ _)

end StatMech.Onsager
