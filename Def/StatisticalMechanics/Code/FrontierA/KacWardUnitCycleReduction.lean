/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnitCycleReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardTrivalentFormalAssembly.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager

universe u


noncomputable def kwGraphLoopWalk
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart)
    (hvalid : ∀ k, G.DartAdj (loop k) (loop (k + 1))) :
    G.Walk (loop 0).fst (loop 0).fst := by
  let darts := List.ofFn loop
  have hdarts : darts ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_ofFn]
    exact NeZero.pos n
  have hclosed : List.IsChain G.DartAdj (darts ++ [loop 0]) := by
    exact StatMech.Onsager.ons_isChain_closed_ofFn_mk loop hvalid
  have hchain : List.IsChain G.DartAdj darts := by
    have := hclosed.dropLast
    simpa [darts] using this
  let walk := SimpleGraph.Walk.ofDarts darts hdarts hchain
  refine walk.copy ?_ ?_
  · change (darts.head hdarts).fst = (loop 0).fst
    simp only [darts, List.head_ofFn]
    congr 2
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    have hlast := hvalid (Fin.last m)
    change (darts.getLast hdarts).snd = (loop 0).fst
    simpa only [darts, List.getLast_ofFn, Nat.succ_sub_one,
      Fin.last_add_one] using hlast

end StatMech.FrontierA
