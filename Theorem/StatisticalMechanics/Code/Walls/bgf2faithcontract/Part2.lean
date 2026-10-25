/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.baoallopen.Part2
import Theorem.StatisticalMechanics.Code.Walls.bcvcutvertex.Part3
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Def.StatisticalMechanics.Code.Walls.bgf2faithcontract.Part2
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


theorem bgf2_ascend {L : ℕ} {c : Site 2} {ω : ConfigSpace (Sym2 (Site 2))}
    (hopen : bgf2_AllOpenAt ω L c) {x : Site 2} (hx : bgf2_inBox L c x) (j : Fin 2) :
    ∀ (k : ℕ) (a : ℤ), (a - c j).natAbs ≤ L → (a + (k : ℤ) - c j).natAbs ≤ L →
      Connected 2 ω (Function.update x j a) (Function.update x j (a + (k : ℤ))) := by
  intro k
  induction k with
  | zero => intro a _ _; simpa using connected_rfl
  | succ m ih =>
    intro a ha hak
    have hint : (a + (m : ℤ) - c j).natAbs ≤ L := by push_cast at hak ⊢; omega
    have hstep : Connected 2 ω (Function.update x j (a + (m : ℤ)))
        (Function.update x j (a + (m : ℤ) + 1)) := by
      have hin1 : bgf2_inBox L c (Function.update x j (a + (m : ℤ))) :=
        bgf2_update_inBox hx j hint
      have hin2 : bgf2_inBox L c (Function.update x j (a + (m : ℤ) + 1)) := by
        refine bgf2_update_inBox hx j ?_
        have : a + ((m : ℤ) + 1) - c j = a + (m : ℤ) + 1 - c j := by ring
        push_cast at hak ⊢; omega
      have hadj := adj_update_succ x j (a + (m : ℤ))
      exact SimpleGraph.Adj.reachable (G := openSubgraph 2 ω)
        (by rw [openSubgraph_adj]; exact ⟨hadj, hopen _ _ hin1 hin2 hadj⟩)
    have hrec := (ih a ha hint).trans hstep
    have he : a + (m : ℤ) + 1 = a + ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    rwa [he] at hrec


theorem bgf2_update_conn {L : ℕ} {c : Site 2} {ω : ConfigSpace (Sym2 (Site 2))}
    (hopen : bgf2_AllOpenAt ω L c) {x : Site 2} (hx : bgf2_inBox L c x) (j : Fin 2) {a : ℤ}
    (ha : (a - c j).natAbs ≤ L) : Connected 2 ω x (Function.update x j a) := by
  have hxj : (x j - c j).natAbs ≤ L := hx j
  have hxupd : Function.update x j (x j) = x := Function.update_eq_self j x
  rcases le_total (x j) a with hle | hle
  · obtain ⟨k, hk⟩ := Int.le.dest hle
    have h := bgf2_ascend hopen hx j k (x j) hxj (by rw [hk]; exact ha)
    rwa [hxupd, hk] at h
  · obtain ⟨k, hk⟩ := Int.le.dest hle
    have h := bgf2_ascend hopen hx j k a ha (by rw [hk]; exact hxj)
    rw [hk, hxupd] at h
    exact h.symm


theorem bgf2_mix_conn {L : ℕ} {c : Site 2} {ω : ConfigSpace (Sym2 (Site 2))}
    (hopen : bgf2_AllOpenAt ω L c) {x y : Site 2} (hx : bgf2_inBox L c x) (hy : bgf2_inBox L c y) :
    ∀ k, k ≤ 2 → Connected 2 ω x (mixSite x y k) := by
  intro k
  induction k with
  | zero => intro _; rw [mixSite_zero]
  | succ m ih =>
    intro hsucc
    have hm : m < 2 := by omega
    have h1 := ih (by omega)
    have hstep : Connected 2 ω (mixSite x y m) (mixSite x y (m + 1)) := by
      rw [mixSite_succ hm]
      exact bgf2_update_conn hopen (bgf2_mix_inBox hx hy m) ⟨m, hm⟩ (hy ⟨m, hm⟩)
    exact h1.trans hstep


theorem bgf2_boxCentre_connected {L : ℕ} {c : Site 2} {ω : ConfigSpace (Sym2 (Site 2))}
    (hopen : bgf2_AllOpenAt ω L c) {a b : Site 2} (ha : bgf2_inBox L c a) (hb : bgf2_inBox L c b) :
    Connected 2 ω a b := by
  have h := bgf2_mix_conn hopen ha hb 2 le_rfl
  rwa [mixSite_full] at h

#check @bgf2_boxCentre_connected


end StatMech.Walls
