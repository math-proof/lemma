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
import Def.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part6
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls

variable {W : Type*} [Fintype W] [DecidableEq W]


variable {V : Type*} [Fintype V] [DecidableEq V]


theorem ghsvp_vertexZ_fieldSet_eq_two_mul_tZ
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : Real) (A : Finset V) :
    ghsvp_vertexZ (withGhost G).edgeFinset
        (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (ghsvp_fieldSet A) =
      2 * ghsvp_tZ G β h A := by
  unfold ghsvp_vertexZ ZJ
  rw [FieldGhostDict.sum_option_config, Fintype.sum_bool]
  have htrue :
      (∑ τ : V -> Bool,
        wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A))
          (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (fun _ => 0)
          (fun z => Option.rec true τ z)) = ghsvp_tZ G β h A := by
    unfold ghsvp_tZ ZJ
    apply Finset.sum_congr rfl
    intro τ hτ
    rw [ghsvp_fieldSet_weight_eq]
    congr 2
    funext x
    simp [FieldGhostDict.split_ghost_spin]
  have hfalse :
      (∑ τ : V -> Bool,
        wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A))
          (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (fun _ => 0)
          (fun z => Option.rec false τ z)) = ghsvp_tZ G β h A := by
    rw [show (∑ τ : V -> Bool,
        wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A))
          (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (fun _ => 0)
          (fun z => Option.rec false τ z)) =
        ZJ (ghsvp_vertexEdges G.edgeFinset A) (fun _ => 2 * β)
          (fun x => -(if x ∈ A then 2 * β * h else 0)) by
      unfold ZJ
      apply Finset.sum_congr rfl
      intro τ hτ
      rw [ghsvp_fieldSet_weight_eq]
      congr 2
      funext x
      by_cases hx : x ∈ A <;> simp [hx, FieldGhostDict.split_ghost_spin]]
    rw [ghsvp_ZJ_negField]
    rfl
  rw [htrue, hfalse]
  ring

theorem ghsvp_vertexZ_someSet_eq_two_mul_uZ
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : Real) (A : Finset V) :
    ghsvp_vertexZ (withGhost G).edgeFinset
        (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (ghsvp_someSet A) =
      2 * ghsvp_uZ G β A := by
  unfold ghsvp_vertexZ ZJ
  rw [FieldGhostDict.sum_option_config, Fintype.sum_bool]
  have hb : ∀ b : Bool,
      (∑ τ : V -> Bool,
        wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_someSet A))
          (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (fun _ => 0)
          (fun z => Option.rec b τ z)) = ghsvp_uZ G β A := by
    intro b
    unfold ghsvp_uZ ZJ
    apply Finset.sum_congr rfl
    intro τ hτ
    exact ghsvp_someSet_weight_eq G β h A (fun z => Option.rec b τ z)
  rw [hb, hb]
  ring

theorem ghsvp_subsetMass_eq_four_mul_tZ_uZ
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : Real) (A : Finset V) :
    ghsvp_subsetMass G β h A =
      4 * (ghsvp_tZ G β h A * ghsvp_uZ G β Aᶜ) := by
  unfold ghsvp_subsetMass
  dsimp only
  rw [ghsvp_vertexZ_fieldSet_eq_two_mul_tZ, ghsvp_vertexZ_someSet_eq_two_mul_uZ]
  ring


theorem ghsvp_subsetMass_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (A : Finset V) : 0 <= ghsvp_subsetMass G β h A := by
  unfold ghsvp_subsetMass
  exact mul_nonneg (ZJ_pos _ _ _).le (ZJ_pos _ _ _).le


theorem ghsvp_subsetMass_logSupermodular (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (hβ : 0 <= β) (hh : 0 <= h) (A B : Finset V) :
    ghsvp_subsetMass G β h A * ghsvp_subsetMass G β h B <=
      ghsvp_subsetMass G β h (A ∪ B) * ghsvp_subsetMass G β h (A ∩ B) := by
  let J2 : Sym2 (Option V) -> Real := ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)
  have hJ2 : forall e, 0 <= J2 e := by
    intro e
    induction e with
    | h a b =>
      rcases a with _ | a <;> rcases b with _ | b <;>
        simp [J2, ghostCoupling] <;> positivity
  have hnd : ∀ e ∈ (withGhost G).edgeFinset, ¬ e.IsDiag := by
    intro e he
    exact SimpleGraph.not_isDiag_of_mem_edgeFinset he
  have hp := ghsvp_vertexZ_logSupermodular (withGhost G).edgeFinset J2 hJ2 hnd
    (ghsvp_fieldSet A) (ghsvp_fieldSet B)
  have hz := ghsvp_vertexZ_logSupermodular (withGhost G).edgeFinset J2 hJ2 hnd
    (ghsvp_someSet Aᶜ) (ghsvp_someSet Bᶜ)
  rw [← ghsvp_fieldSet_union, ← ghsvp_fieldSet_inter] at hp
  have hcu : Aᶜ ∪ Bᶜ = (A ∩ B)ᶜ := by ext x; simp
  have hci : Aᶜ ∩ Bᶜ = (A ∪ B)ᶜ := by ext x; simp
  rw [← ghsvp_someSet_union, ← ghsvp_someSet_inter, hcu, hci] at hz
  unfold ghsvp_subsetMass
  change
    (ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet A) *
        ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_someSet Aᶜ)) *
      (ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet B) *
        ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_someSet Bᶜ)) <= _
  have hnon1 : 0 <= ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet (A ∪ B)) :=
    (ZJ_pos _ _ _).le
  have hnon2 : 0 <= ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet (A ∩ B)) :=
    (ZJ_pos _ _ _).le
  have hprod := mul_le_mul hp hz
    (mul_nonneg (ZJ_pos _ _ _).le (ZJ_pos _ _ _).le)
    (mul_nonneg hnon1 hnon2)
  nlinarith [hprod]


end StatMech.Ising
