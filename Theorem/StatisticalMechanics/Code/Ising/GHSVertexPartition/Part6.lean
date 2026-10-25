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
import Def.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part5
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls

variable {W : Type*} [Fintype W] [DecidableEq W]


variable {V : Type*} [Fintype V] [DecidableEq V]


lemma ghsvp_someSet_mono : Monotone (ghsvp_someSet : Finset V -> Finset (Option V)) := by
  intro A B hAB
  intro z hz
  rw [ghsvp_someSet, Finset.mem_map] at hz ⊢
  obtain ⟨x, hx, rfl⟩ := hz
  exact ⟨x, hAB hx, rfl⟩

lemma ghsvp_someSet_inter (A B : Finset V) :
    ghsvp_someSet (A ∩ B) = ghsvp_someSet A ∩ ghsvp_someSet B := by
  ext z
  rcases z with _ | z <;> simp [ghsvp_someSet]

lemma ghsvp_someSet_union (A B : Finset V) :
    ghsvp_someSet (A ∪ B) = ghsvp_someSet A ∪ ghsvp_someSet B := by
  ext z
  rcases z with _ | z <;> simp [ghsvp_someSet]

lemma ghsvp_fieldSet_inter (A B : Finset V) :
    ghsvp_fieldSet (A ∩ B) = ghsvp_fieldSet A ∩ ghsvp_fieldSet B := by
  ext z
  rcases z with _ | z <;> simp [ghsvp_fieldSet, ghsvp_someSet]

lemma ghsvp_fieldSet_union (A B : Finset V) :
    ghsvp_fieldSet (A ∪ B) = ghsvp_fieldSet A ∪ ghsvp_fieldSet B := by
  ext z
  rcases z with _ | z <;> simp [ghsvp_fieldSet, ghsvp_someSet]

lemma ghsvp_edgeInside_map_some_iff (A : Finset V) (e : Sym2 V) :
    Sharpness.edgeInside (ghsvp_fieldSet A) (Sym2.map some e) ↔
      Sharpness.edgeInside A e := by
  induction e with
  | h x y => simp [Sharpness.edgeInside, ghsvp_fieldSet, ghsvp_someSet]

lemma ghsvp_origEdges_filter_fieldSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) :
    (FieldGhostDict.origEdges G).filter (Sharpness.edgeInside (ghsvp_fieldSet A)) =
      (ghsvp_vertexEdges G.edgeFinset A).image (Sym2.map some) := by
  rw [FieldGhostDict.origEdges, Finset.filter_image]
  unfold ghsvp_vertexEdges
  congr 1
  ext e
  simp [ghsvp_edgeInside_map_some_iff]

lemma ghsvp_ghostEdges_filter_fieldSet (A : Finset V) :
    (FieldGhostDict.ghostEdges V).filter (Sharpness.edgeInside (ghsvp_fieldSet A)) =
      A.image (fun x => s(some x, none)) := by
  ext e
  induction e with
  | h x y =>
    rcases x with _ | x <;> rcases y with _ | y <;>
      simp [FieldGhostDict.ghostEdges, Sharpness.edgeInside,
        ghsvp_fieldSet, ghsvp_someSet]


theorem ghsvp_fieldSet_couplingSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (A : Finset V) (s : ConfigSpace (Option V)) :
    (∑ e ∈ ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A),
        ghostCoupling (2 * β * h) 1 (fun _ => 2 * β) e * bond s e) =
      (∑ e ∈ ghsvp_vertexEdges G.edgeFinset A,
          (2 * β) * bond (fun x => s (some x)) e) +
        (2 * β * h) * spin s none * ∑ x ∈ A, spin s (some x) := by
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
        rw [Sym2.map_mk, ghostCoupling_some_some, bond_mk, bond_mk]
        rfl
    · intro a _ b _ hab
      exact Sym2.map.injective (Option.some_injective V) hab
  · rw [Finset.sum_image]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [ghostCoupling_some_none, bond_mk]
      ring
    · intro a _ b _ hab
      rw [Sym2.eq_iff] at hab
      rcases hab with h | h
      · exact Option.some_injective V h.1
      · exact absurd h.2 (by simp)

theorem ghsvp_fieldSet_weight_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (A : Finset V) (s : ConfigSpace (Option V)) :
    wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A))
        (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (fun _ => 0) s =
      wJ (ghsvp_vertexEdges G.edgeFinset A) (fun _ => 2 * β)
        (fun x => if x ∈ A then (2 * β * h) * spin s none else 0)
        (fun x => s (some x)) := by
  unfold wJ
  rw [ghsvp_fieldSet_couplingSum]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  congr 2
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter, Finset.mul_sum]
  simp
  apply Finset.sum_congr rfl
  intro x hx
  rfl

lemma ghsvp_edgeInside_map_someSet_iff (A : Finset V) (e : Sym2 V) :
    Sharpness.edgeInside (ghsvp_someSet A) (Sym2.map some e) ↔
      Sharpness.edgeInside A e := by
  induction e with
  | h x y => simp [Sharpness.edgeInside, ghsvp_someSet]

lemma ghsvp_origEdges_filter_someSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) :
    (FieldGhostDict.origEdges G).filter (Sharpness.edgeInside (ghsvp_someSet A)) =
      (ghsvp_vertexEdges G.edgeFinset A).image (Sym2.map some) := by
  rw [FieldGhostDict.origEdges, Finset.filter_image]
  unfold ghsvp_vertexEdges
  congr 1
  ext e
  simp [ghsvp_edgeInside_map_someSet_iff]

lemma ghsvp_ghostEdges_filter_someSet (A : Finset V) :
    (FieldGhostDict.ghostEdges V).filter (Sharpness.edgeInside (ghsvp_someSet A)) = ∅ := by
  ext e
  induction e with
  | h x y =>
    rcases x with _ | x <;> rcases y with _ | y <;>
      simp [FieldGhostDict.ghostEdges, Sharpness.edgeInside, ghsvp_someSet]

theorem ghsvp_someSet_weight_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (A : Finset V) (s : ConfigSpace (Option V)) :
    wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_someSet A))
        (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (fun _ => 0) s =
      wJ (ghsvp_vertexEdges G.edgeFinset A) (fun _ => 2 * β) (fun _ => 0)
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
      rw [Sym2.map_mk, ghostCoupling_some_some, bond_mk, bond_mk]
      rfl
  · intro a _ b _ hab
    exact Sym2.map.injective (Option.some_injective V) hab

theorem ghsvp_wJ_negField_flip (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hf : V -> Real) (s : ConfigSpace V) :
    wJ E J (fun x => -hf x) (FieldGhostDict.flipV s) = wJ E J hf s := by
  unfold wJ
  congr 2
  · apply Finset.sum_congr rfl
    intro e he
    rw [FieldGhostDict.bond_flipV]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [FieldGhostDict.spin_flipV]
    ring

theorem ghsvp_ZJ_negField (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hf : V -> Real) : ZJ E J (fun x => -hf x) = ZJ E J hf := by
  unfold ZJ
  rw [← Equiv.sum_comp (FieldGhostDict.flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  apply Finset.sum_congr rfl
  intro s hs
  exact ghsvp_wJ_negField_flip E J hf s


end StatMech.Ising
