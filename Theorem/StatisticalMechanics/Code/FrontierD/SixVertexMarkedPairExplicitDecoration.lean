/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem card_complement_subtype
    {Site : Type*} [Fintype Site] [DecidableEq Site]
    (marked : Finset Site) :
    Fintype.card {site : Site // site ∉ marked} =
      Fintype.card Site - marked.card := by
  rw [Fintype.card_subtype_compl]
  congr 1
  rw [Fintype.card_subtype]
  simp

theorem card_marked_finsets
    (Site : Type*) [Fintype Site] [DecidableEq Site] (k : Nat) :
    Fintype.card {s : Finset Site // s.card = k} =
      (Fintype.card Site).choose k := by
  rw [Fintype.card_subtype]
  rw [show (Finset.univ.filter fun s : Finset Site => s.card = k) =
      Finset.univ.powersetCard k by
    ext s
    simp]
  rw [Finset.card_powersetCard]
  simp

theorem card_markedBinaryDecoration
    (Site : Type*) [Fintype Site] [DecidableEq Site] (k : Nat) :
    Fintype.card (MarkedBinaryDecoration Site k) =
      2 ^ (Fintype.card Site - k) * (Fintype.card Site).choose k := by
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_fun, Fintype.card_bool,
    card_complement_subtype]
  have hcard (marked : {s : Finset Site // s.card = k}) :
      Fintype.card Site - marked.1.card = Fintype.card Site - k := by
    rw [marked.2]
  simp_rw [hcard]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    card_marked_finsets]
  exact Nat.mul_comm _ _


end
end StatMech.FrontierD
