/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomVertexPartition.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeSum
import Theorem.StatisticalMechanics.Code.Sharpness.GHSConcavity
import Def.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part2
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option maxHeartbeats 2400000


namespace StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsi_bondSum_split (K : Sym2 V → ℝ) (q a : ConfigSpace V) :
    (∑ e ∈ G.edgeFinset, K e * bond a e) +
        ∑ e ∈ G.edgeFinset, K e * bond (ghsLMate q a) e =
      (∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q),
          (2 * K e) * bond a e) +
        ∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ,
          (2 * K e) * bond a e := by
  rw [← Finset.sum_add_distrib]
  simp_rw [← mul_add, ghsL_bond_add_mate]
  unfold ghsvp_vertexEdges
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hA : edgeInside (ghsLAgreeFinset q) e
  · have hAc : ¬ edgeInside (ghsLAgreeFinset q)ᶜ e := by
      induction e with
      | h x y => simp_all [edgeInside]
    simp [hA, hAc]
    ring
  · by_cases hAc : edgeInside (ghsLAgreeFinset q)ᶜ e
    · simp [hA, hAc]
      ring
    · simp [hA, hAc]


theorem ghsi_fieldSum_split (hf : V → ℝ) (q a : ConfigSpace V) :
    (∑ v : V, hf v * spin a v) +
        ∑ v : V, hf v * spin (ghsLMate q a) v =
      ∑ v ∈ ghsLAgreeFinset q, (2 * hf v) * spin a v := by
  rw [← Finset.sum_add_distrib]
  simp_rw [← mul_add, ghsL_spin_add_mate]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  unfold ghsLAgreeFinset
  apply Finset.sum_congr rfl
  intro v _
  ring


theorem ghsi_duplicateWeight_eq_tWeight_mul_uWeight
    (K : Sym2 V → ℝ) (hf : V → ℝ) (q a : ConfigSpace V) :
    wJ G.edgeFinset K hf a * wJ G.edgeFinset K hf (ghsLMate q a) =
      ghsiTWeight G K hf q a * ghsiUWeight G K q a := by
  unfold wJ ghsiTWeight ghsiUWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [show
      (∑ e ∈ G.edgeFinset, K e * bond a e) + (∑ x, hf x * spin a x) +
          ((∑ e ∈ G.edgeFinset, K e * bond (ghsLMate q a) e) +
            ∑ x, hf x * spin (ghsLMate q a) x) =
        ((∑ e ∈ G.edgeFinset, K e * bond a e) +
          ∑ e ∈ G.edgeFinset, K e * bond (ghsLMate q a) e) +
        ((∑ x, hf x * spin a x) +
          ∑ x, hf x * spin (ghsLMate q a) x) by ring]
  rw [ghsi_bondSum_split G K q a, ghsi_fieldSum_split hf q a]
  ring


theorem ghsiTWeight_split (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q a : ConfigSpace V) :
    ghsiTWeight G K hf q a =
      ghsiTWeight G K hf q (ghsLTComplete q (ghsLSplitEquiv q a).1) := by
  unfold ghsiTWeight
  congr 2
  · apply Finset.sum_congr rfl
    intro e he
    have hi := (Finset.mem_filter.mp he).2
    induction e with
    | h x y =>
      have hx : q x = true := mem_ghsLAgreeFinset q x |>.mp (hi x (by simp))
      have hy : q y = true := mem_ghsLAgreeFinset q y |>.mp (hi y (by simp))
      simp only [bond_mk]
      congr 2 <;> unfold spin
      · rw [ghsLTComplete_eq_on q a hx]
      · rw [ghsLTComplete_eq_on q a hy]
  · apply Finset.sum_congr rfl
    intro v hv
    have hq := (mem_ghsLAgreeFinset q v).mp hv
    congr 1
    unfold spin
    rw [ghsLTComplete_eq_on q a hq]


theorem ghsiUWeight_split (K : Sym2 V → ℝ) (q a : ConfigSpace V) :
    ghsiUWeight G K q a =
      ghsiUWeight G K q (ghsLUComplete q (ghsLSplitEquiv q a).2) := by
  unfold ghsiUWeight
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  have hi := (Finset.mem_filter.mp he).2
  induction e with
  | h x y =>
    have hx : ¬ q x = true := by
      simpa using (Finset.mem_compl.mp (hi x (by simp)))
    have hy : ¬ q y = true := by
      simpa using (Finset.mem_compl.mp (hi y (by simp)))
    simp only [bond_mk]
    congr 2 <;> unfold spin
    · rw [ghsLUComplete_eq_on q a hx]
    · rw [ghsLUComplete_eq_on q a hy]


theorem ghsiTWeight_eq_wJ_restricted (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q a : ConfigSpace V) :
    ghsiTWeight G K hf q a =
      wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
        (fun e => 2 * K e)
        (fun x => if x ∈ ghsLAgreeFinset q then 2 * hf x else 0) a := by
  unfold ghsiTWeight wJ
  congr 1
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter, Finset.filter_univ_mem]


theorem ghsiUWeight_eq_wJ (K : Sym2 V → ℝ) (q a : ConfigSpace V) :
    ghsiUWeight G K q a =
      wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ)
        (fun e => 2 * K e) (fun _ => 0) a := by
  unfold ghsiUWeight wJ
  simp


end StatMech.Ising
