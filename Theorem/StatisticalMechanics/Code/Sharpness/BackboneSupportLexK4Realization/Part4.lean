/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization.Part4
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

@[simp] theorem shbK4Edge_mem_oddSupport
    (E : Finset shbK4Edge) (n : Current (Fin 4)) (k : shbK4Edge) :
    k ∈ shbK4OddSupport E n ↔ k ∈ E ∧ Odd (n k.code) := by
  simp [shbK4OddSupport]

theorem shbK4Edge_mem_code_iff_incident (k : shbK4Edge) (v : Fin 4) :
    v ∈ k.code ↔ k.Incident v := by
  fin_cases k <;> fin_cases v <;> decide

theorem shbK4_incidentFlux_eq
    (E : Finset shbK4Edge) (n : Current (Fin 4)) (v : Fin 4) :
    incidentFlux (shbK4Graph E) n v =
      ∑ k ∈ E.filter (fun k ↦ k.Incident v), n k.code := by
  unfold incidentFlux
  rw [shbK4Graph_edgeFinset]
  rw [Finset.sum_filter]
  rw [Finset.sum_filter]
  rw [Finset.sum_image shbK4Edge.code_injective.injOn]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [shbK4Edge_mem_code_iff_incident]


theorem shbK4_sources_eq_boundary
    (E : Finset shbK4Edge) (n : Current (Fin 4)) :
    sources (shbK4Graph E) n = shbK4Boundary (shbK4OddSupport E n) := by
  ext v
  rw [mem_sources]
  unfold shbK4Boundary
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [shbK4_incidentFlux_eq]
  rw [Finset.odd_sum_iff_odd_card_odd]
  have hfilter :
      (E.filter (fun k ↦ k.Incident v)).filter (fun k ↦ Odd (n k.code)) =
        (shbK4OddSupport E n).filter (fun k ↦ k.Incident v) := by
    ext k
    simp [shbK4OddSupport, and_left_comm, and_assoc, and_comm]
  rw [hfilter]


end StatMech.Sharpness
