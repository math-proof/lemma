/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingSquareTorusAdapter.Part5
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


@[simp] theorem quantumIsingSquareTorusCoupling_horizontal
    (beta h : Real) (L : Nat) [Fact (2 < L)]
    (p : ZMod L × ZMod L) :
    quantumIsingSquareTorusCoupling beta h L (ons_portEdge L (p, 0)) =
      beta / (4 * L) := by
  rw [quantumIsingSquareTorusCoupling, if_pos]
  exact ⟨p, rfl⟩

@[simp] theorem quantumIsingSquareTorusCoupling_vertical
    (beta h : Real) (L : Nat) [Fact (2 < L)]
    (p : ZMod L × ZMod L) :
    quantumIsingSquareTorusCoupling beta h L (ons_portEdge L (p, 1)) =
      quantumIsingVerticalCoupling beta h L := by
  rw [quantumIsingSquareTorusCoupling, if_neg]
  rintro ⟨q, hq⟩
  have heq := (ons_portEdge_eq_iff L (p, 1) (q, 0)).mp hq.symm
  rcases heq with heq | heq
  · have hdir := congrArg Prod.snd heq
    norm_num at hdir
  · have hdir := congrArg Prod.snd heq
    simp [ons_dartRev] at hdir

theorem sum_zmod_square_eq_fin_square
    (L : Nat) [NeZero L]
    (f : ZMod L × ZMod L → Real) :
    (∑ p : ZMod L × ZMod L, f p) =
      ∑ k : Fin L, ∑ i : Fin L,
        f (ZMod.finEquiv L i, ZMod.finEquiv L k) := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : ZMod L, ∑ y : ZMod L, f (x, y)) =
        ∑ i : Fin L, ∑ y : ZMod L,
          f (ZMod.finEquiv L i, y) :=
      (Equiv.sum_comp (ZMod.finEquiv L).toEquiv
        (fun x : ZMod L ↦ ∑ y : ZMod L, f (x, y))).symm
    _ = ∑ i : Fin L, ∑ k : Fin L,
          f (ZMod.finEquiv L i, ZMod.finEquiv L k) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Equiv.sum_comp (ZMod.finEquiv L).toEquiv
        (fun y : ZMod L ↦ f (ZMod.finEquiv L i, y))).symm
    _ = _ := Finset.sum_comm


end StatMech.FrontierA
