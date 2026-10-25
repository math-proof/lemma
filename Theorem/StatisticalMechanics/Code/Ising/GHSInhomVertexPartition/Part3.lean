/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Def.StatisticalMechanics.Code.Ising.GHSInhomVertexPartition.Part3
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem ghsiSubsetMass_eq_four_mul_tZ_uZ
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V) :
    ghsiSubsetMass G K hf A = 4 * (ghsiTZ G K hf A * ghsiUZ G K Aᶜ) := by
  unfold ghsiSubsetMass
  rw [ghsi_vertexZ_fieldSet_eq_two_mul_tZ,
    ghsi_vertexZ_someSet_eq_two_mul_uZ]
  ring

theorem ghsiSubsetMass_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V) :
    0 ≤ ghsiSubsetMass G K hf A := by
  unfold ghsiSubsetMass
  exact mul_nonneg (ZJ_pos _ _ _).le (ZJ_pos _ _ _).le


theorem ghsiSubsetMass_logSupermodular
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hhf : ∀ x, 0 ≤ hf x) (A B : Finset V) :
    ghsiSubsetMass G K hf A * ghsiSubsetMass G K hf B ≤
      ghsiSubsetMass G K hf (A ∪ B) * ghsiSubsetMass G K hf (A ∩ B) := by
  let J2 : Sym2 (Option V) → ℝ := ghsiGhostCoupling K hf
  have hJ2 : ∀ e, 0 ≤ J2 e := by
    intro e
    induction e with
    | h a b =>
      rcases a with _ | a <;> rcases b with _ | b <;>
        simp [J2, ghsiGhostCoupling, hK, hhf]
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
  unfold ghsiSubsetMass
  change
    (ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet A) *
        ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_someSet Aᶜ)) *
      (ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet B) *
        ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_someSet Bᶜ)) ≤ _
  have hnon1 :
      0 ≤ ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet (A ∪ B)) :=
    (ZJ_pos _ _ _).le
  have hnon2 :
      0 ≤ ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet (A ∩ B)) :=
    (ZJ_pos _ _ _).le
  have hprod := mul_le_mul hp hz
    (mul_nonneg (ZJ_pos _ _ _).le (ZJ_pos _ _ _).le)
    (mul_nonneg hnon1 hnon2)
  nlinarith [hprod]

end StatMech.Ising
