/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Walls.ghysupermult.Part2
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part3
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls

variable {W : Type*} [Fintype W] [DecidableEq W]


def ghsvp_mergeConfig (S : Finset W) (a : (↑S -> Bool))
    (b : ({v : W // v ∉ S}) -> Bool) : ConfigSpace W :=
  fun v => if hv : v ∈ S then a ⟨v, hv⟩ else b ⟨v, hv⟩


def ghsvp_splitConfig (S : Finset W) :
    ConfigSpace W ≃ ((↑S -> Bool) × (({v : W // v ∉ S}) -> Bool)) where
  toFun s := (λ v => s v, λ v => s v)
  invFun p := ghsvp_mergeConfig S p.1 p.2
  left_inv s := by
    funext v
    simp only [ghsvp_mergeConfig]
    split <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext v
      simp [ghsvp_mergeConfig, v.property]
    · funext v
      simp [ghsvp_mergeConfig, v.property]


end StatMech.Ising
