/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Def.StatisticalMechanics.Code.Ising.GHSInhomVertexPartition.Part2
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem ghsi_fieldSet_couplingSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V)
    (s : ConfigSpace (Option V)) :
    (∑ e ∈ ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A),
        ghsiGhostCoupling K hf e * bond s e) =
      (∑ e ∈ ghsvp_vertexEdges G.edgeFinset A,
          (2 * K e) * bond (fun x => s (some x)) e) +
        spin s none * ∑ x ∈ A, (2 * hf x) * spin s (some x) := by
  unfold ghsvp_vertexEdges
  rw [FieldGhostDict.withGhost_edgeFinset_eq, Finset.filter_union,
    ghsvp_origEdges_filter_fieldSet, ghsvp_ghostEdges_filter_fieldSet]
  have hdisj : Disjoint
      ((ghsvp_vertexEdges G.edgeFinset A).image (Sym2.map some))
      (A.image (fun x => s(some x, none))) := by
    apply (FieldGhostDict.disjoint_orig_ghost G).mono
    · intro e he
      exact Finset.mem_filter.mp (by
        rw [ghsvp_origEdges_filter_fieldSet]
        exact he) |>.1
    · intro e he
      exact Finset.mem_filter.mp (by
        rw [ghsvp_ghostEdges_filter_fieldSet]
        exact he) |>.1
  rw [Finset.sum_union hdisj]
  congr 1
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro e _
      induction e with
      | h x y =>
        rw [Sym2.map_mk, ghsiGhostCoupling_some_some, bond_mk, bond_mk]
        rfl
    · intro a _ b _ hab
      exact Sym2.map.injective (Option.some_injective V) hab
  · rw [Finset.sum_image]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [ghsiGhostCoupling_some_none, bond_mk]
      ring
    · intro a _ b _ hab
      rw [Sym2.eq_iff] at hab
      rcases hab with h | h
      · exact Option.some_injective V h.1
      · exact absurd h.2 (by simp)


theorem ghsi_fieldSet_weight_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V)
    (s : ConfigSpace (Option V)) :
    wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A))
        (ghsiGhostCoupling K hf) (fun _ => 0) s =
      wJ (ghsvp_vertexEdges G.edgeFinset A) (fun e => 2 * K e)
        (fun x => if x ∈ A then (2 * hf x) * spin s none else 0)
        (fun x => s (some x)) := by
  unfold wJ
  rw [ghsi_fieldSet_couplingSum]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  congr 2
  rw [Finset.mul_sum]
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  rw [Finset.filter_univ_mem]
  simp only [spin]
  ring_nf


theorem ghsi_someSet_weight_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V)
    (s : ConfigSpace (Option V)) :
    wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_someSet A))
        (ghsiGhostCoupling K hf) (fun _ => 0) s =
      wJ (ghsvp_vertexEdges G.edgeFinset A) (fun e => 2 * K e) (fun _ => 0)
        (fun x => s (some x)) := by
  have hedges :
      ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_someSet A) =
        (ghsvp_vertexEdges G.edgeFinset A).image (Sym2.map some) := by
    unfold ghsvp_vertexEdges
    rw [FieldGhostDict.withGhost_edgeFinset_eq, Finset.filter_union,
      ghsvp_origEdges_filter_someSet, ghsvp_ghostEdges_filter_someSet]
    simp [ghsvp_vertexEdges]
  unfold wJ
  rw [hedges, Finset.sum_image]
  · simp only [zero_mul, Finset.sum_const_zero, add_zero]
    congr 2
    funext e
    induction e with
    | h x y =>
      rw [Sym2.map_mk, ghsiGhostCoupling_some_some, bond_mk, bond_mk]
      rfl
  · intro a _ b _ hab
    exact Sym2.map.injective (Option.some_injective V) hab


theorem ghsi_vertexZ_fieldSet_eq_two_mul_tZ
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V) :
    ghsvp_vertexZ (withGhost G).edgeFinset (ghsiGhostCoupling K hf)
        (ghsvp_fieldSet A) = 2 * ghsiTZ G K hf A := by
  unfold ghsvp_vertexZ ZJ
  rw [FieldGhostDict.sum_option_config, Fintype.sum_bool]
  have htrue :
      (∑ tau : V → Bool,
        wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A))
          (ghsiGhostCoupling K hf) (fun _ => 0)
          (fun z => Option.rec true tau z)) = ghsiTZ G K hf A := by
    unfold ghsiTZ ZJ
    apply Finset.sum_congr rfl
    intro tau _
    rw [ghsi_fieldSet_weight_eq]
    congr 2
    funext x
    simp [FieldGhostDict.split_ghost_spin]
  have hfalse :
      (∑ tau : V → Bool,
        wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A))
          (ghsiGhostCoupling K hf) (fun _ => 0)
          (fun z => Option.rec false tau z)) = ghsiTZ G K hf A := by
    rw [show (∑ tau : V → Bool,
        wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A))
          (ghsiGhostCoupling K hf) (fun _ => 0)
          (fun z => Option.rec false tau z)) =
        ZJ (ghsvp_vertexEdges G.edgeFinset A) (fun e => 2 * K e)
          (fun x => -(if x ∈ A then 2 * hf x else 0)) by
      unfold ZJ
      apply Finset.sum_congr rfl
      intro tau _
      rw [ghsi_fieldSet_weight_eq]
      congr 2
      funext x
      by_cases hx : x ∈ A <;> simp [hx, FieldGhostDict.split_ghost_spin]]
    rw [ghsvp_ZJ_negField]
    rfl
  rw [htrue, hfalse]
  ring


theorem ghsi_vertexZ_someSet_eq_two_mul_uZ
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V) :
    ghsvp_vertexZ (withGhost G).edgeFinset (ghsiGhostCoupling K hf)
        (ghsvp_someSet A) = 2 * ghsiUZ G K A := by
  unfold ghsvp_vertexZ ZJ
  rw [FieldGhostDict.sum_option_config, Fintype.sum_bool]
  have hb : ∀ b : Bool,
      (∑ tau : V → Bool,
        wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_someSet A))
          (ghsiGhostCoupling K hf) (fun _ => 0)
          (fun z => Option.rec b tau z)) = ghsiUZ G K A := by
    intro b
    unfold ghsiUZ ZJ
    apply Finset.sum_congr rfl
    intro tau _
    exact ghsi_someSet_weight_eq G K hf A (fun z => Option.rec b tau z)
  rw [hb, hb]
  ring


end StatMech.Ising
