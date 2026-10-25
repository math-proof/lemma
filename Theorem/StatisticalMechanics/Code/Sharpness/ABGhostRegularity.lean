/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
open Filter Finset Set SimpleGraph Topology
open Asymptotics


namespace StatMech

namespace Sharpness

open ConfigSpace

section FiniteProduct

variable {E : Type*} [Fintype E] [DecidableEq E]


set_option maxHeartbeats 800000 in

theorem abgr_sum_configWeightV (p : E -> Real) :
    ∑ omega : ConfigSpace E, configWeightV p omega = 1 := by
  unfold configWeightV edgeWeightV
  calc
    (∑ omega : E -> Bool, ∏ e : E, if omega e then p e else 1 - p e) =
        ∏ e : E, ∑ b : Bool, if b then p e else 1 - p e :=
      (Fintype.prod_sum (fun e b => if b = true then p e else 1 - p e)).symm
    _ = 1 := by simp


set_option maxHeartbeats 800000 in


theorem abgr_probV_allClosed (p : E -> Real) (t : Finset E) :
    probV p {omega | ∀ e ∈ t, omega e = false} = ∏ e ∈ t, (1 - p e) := by
  let f : E -> Bool -> Real := fun e b =>
    if e ∈ t then (if b then 0 else 1 - p e)
    else (if b then p e else 1 - p e)
  unfold probV configWeightV edgeWeightV
  calc
    (∑ omega : ConfigSpace E,
        {omega | ∀ e ∈ t, omega e = false}.indicator (fun _ => (1 : Real)) omega *
          ∏ e : E, if omega e then p e else 1 - p e) =
        ∑ omega : ConfigSpace E, ∏ e : E, f e (omega e) := by
            apply Finset.sum_congr rfl
            intro omega _
            by_cases hclosed : ∀ e ∈ t, omega e = false
            · have hmem : omega ∈ {omega | ∀ e ∈ t, omega e = false} := hclosed
              rw [Set.indicator_of_mem hmem, one_mul]
              apply Finset.prod_congr rfl
              intro e _
              by_cases he : e ∈ t
              · simp [f, he, hclosed e he]
              · simp [f, he]
            · have hmem : omega ∉ {omega | ∀ e ∈ t, omega e = false} := hclosed
              rw [Set.indicator_of_notMem hmem, zero_mul]
              push_neg at hclosed
              obtain ⟨e, he, hopen⟩ := hclosed
              symm
              apply Finset.prod_eq_zero (Finset.mem_univ e)
              have hopen' : omega e = true := by
                cases h : omega e <;> simp_all
              simp [f, he, hopen']
    _ = ∏ e : E, ∑ b : Bool, f e b := (Fintype.prod_sum f).symm
    _ = ∏ e ∈ t, (1 - p e) := by
      classical
      simp [f]


theorem abgr_probV_anyOpen (p : E -> Real) (t : Finset E) :
    probV p {omega | ∃ e ∈ t, omega e = true} =
      1 - ∏ e ∈ t, (1 - p e) := by
  have hcompl : {omega : ConfigSpace E | ∃ e ∈ t, omega e = true}ᶜ =
      {omega | ∀ e ∈ t, omega e = false} := by
    ext omega
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    push_neg
    simp
  have htotal : probV p {omega : ConfigSpace E | ∃ e ∈ t, omega e = true} +
      probV p ({omega : ConfigSpace E | ∃ e ∈ t, omega e = true}ᶜ) = 1 := by
    unfold probV
    rw [← Finset.sum_add_distrib]
    calc
      (∑ omega : ConfigSpace E,
          ({omega | ∃ e ∈ t, omega e = true}.indicator (fun _ => (1 : Real)) omega *
              configWeightV p omega +
            {omega | ∃ e ∈ t, omega e = true}ᶜ.indicator (fun _ => (1 : Real)) omega *
              configWeightV p omega)) =
          ∑ omega : ConfigSpace E, configWeightV p omega := by
            apply Finset.sum_congr rfl
            intro omega _
            by_cases h : ∃ e ∈ t, omega e = true <;> simp [h]
      _ = 1 := abgr_sum_configWeightV p
  rw [hcompl, abgr_probV_allClosed] at htotal
  linarith


end FiniteProduct
end Sharpness
end StatMech
