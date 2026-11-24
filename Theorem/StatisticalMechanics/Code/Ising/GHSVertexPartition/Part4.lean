module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Inequalities.FKG
public import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
public import Theorem.StatisticalMechanics.Code.Walls.ghysupermult.Part2
public import Def.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part3
open Finset Classical
set_option maxHeartbeats 1600000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls

variable {W : Type*} [Fintype W] [DecidableEq W]


theorem ghsvp_wJ_mergeConfig_independent (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (S : Finset W) (a : ↑S -> Bool) (b c : ({v : W // v ∉ S}) -> Bool) :
    wJ (ghsvp_vertexEdges E S) J (fun _ => 0) (ghsvp_mergeConfig S a b) =
      wJ (ghsvp_vertexEdges E S) J (fun _ => 0) (ghsvp_mergeConfig S a c) := by
  unfold wJ
  congr 2
  · apply Finset.sum_congr rfl
    intro e he
    have hins := (Finset.mem_filter.mp he).2
    congr 1
    induction e with
    | h x y =>
      rw [bond_mk, bond_mk]
      have hx : x ∈ S := hins x (by simp)
      have hy : y ∈ S := hins y (by simp)
      change spin (ghsvp_mergeConfig S a b) x * spin (ghsvp_mergeConfig S a b) y =
        spin (ghsvp_mergeConfig S a c) x * spin (ghsvp_mergeConfig S a c) y
      unfold spin
      simp only [ghsvp_mergeConfig, dif_pos hx, dif_pos hy]
  · simp


end StatMech.Ising
