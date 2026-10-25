/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.FK.OffCentreSandwichProof.Part5
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.style.longLine false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


set_option maxHeartbeats 2000000 in

theorem ocs_wired_bulk_upper (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (u v : boxVerts d (n - Nat.sqrt n - 1)) (hadj : (boxGraph d (n - Nat.sqrt n - 1)).Adj u v) :
    edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2)
        (innerEdgeLE d (Nat.sub_le (n - Nat.sqrt n) 1 |>.trans (Nat.sub_le n (Nat.sqrt n)))
          (s(u, v) : Sym2 (boxVerts d (n - Nat.sqrt n - 1))))
      ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) + ocs_wiredDelta N e' t n := by
  have hR : 1 ≤ Nat.sqrt n := by rw [Nat.one_le_iff_ne_zero, Ne, Nat.sqrt_eq_zero]; omega
  have hRn1 : Nat.sqrt n + 1 ≤ n := by
    have h2 : Nat.sqrt n * Nat.sqrt n ≤ n := by
      have := Nat.sqrt_le' n
      calc Nat.sqrt n * Nat.sqrt n = (Nat.sqrt n) ^ 2 := by ring
        _ ≤ n := this
    nlinarith [Nat.sqrt_le_self n, h2]
  have hmn : n - Nat.sqrt n - 1 ≤ n :=
    Nat.sub_le (n - Nat.sqrt n) 1 |>.trans (Nat.sub_le n (Nat.sqrt n))
  obtain ⟨p0, hp0⟩ := ocs_edge_dir_candMap d (n - Nat.sqrt n - 1) u v hadj
  have c0 := ocs_zero_mem_box d (Nat.sqrt n)
  have cw : ((v : Site d) - (u : Site d)) ∈ box d (Nat.sqrt n) := by
    rw [hp0]; exact ocs_candMap_mem_box d (Nat.sqrt n) hR p0
  have hup := ocs_wired_offCentre_upper d (Nat.sqrt n) n hR hRn1 hmn u v
    (fsc_logistic_pos t) (fsc_logistic_lt_one t) c0 cw
  have hue : (s((⟨(0 : Site d), c0⟩ : boxVerts d (Nat.sqrt n)),
        (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d (Nat.sqrt n))))
      = ocs_unitEdge d (Nat.sqrt n) hR p0 := by
    unfold ocs_unitEdge; congr 1; exact Subtype.ext hp0
  rw [hue] at hup
  have hmarg : ocs_unitWiredMarg d n p0 t
      = edgeMargProb (wiredFkProb (boxGraph d (Nat.sqrt n)) (boxBoundary d (Nat.sqrt n))
          (fsc_logistic t) 2) (ocs_unitEdge d (Nat.sqrt n) hR p0) := by
    unfold ocs_unitWiredMarg; rw [dif_pos hR]
  have hterm : |ocs_unitWiredMarg d n p0 t
        - wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)| ≤ ocs_wiredDelta N e' t n :=
    Finset.single_le_sum
      (f := fun p => |ocs_unitWiredMarg d n p t
        - wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)|)
      (fun p _ => abs_nonneg _) (Finset.mem_univ p0)
  have h1 : ocs_unitWiredMarg d n p0 t
      ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) + ocs_wiredDelta N e' t n := by
    have h2 : ocs_unitWiredMarg d n p0 t
        - wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) ≤ ocs_wiredDelta N e' t n :=
      le_trans (le_abs_self _) hterm
    linarith
  rw [hmarg] at h1
  exact le_trans hup h1

set_option maxHeartbeats 2000000 in

theorem ocs_wiredOffCentreSandwich_of_rotation (hd : 1 ≤ d) (N : ℕ)
    (hres : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_WiredRotationResidue (d := d) N e' t) :
    bdp_WiredOffCentreSandwich (d := d) N := by
  intro e' t
  refine ⟨ocs_wiredBulkSet d, ocs_wiredDelta N e' t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n e he
    rw [ocs_wiredBulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    exact ocs_innerEdgeLE_mem_edgeFinset d _ eb heb
  · exact fun n => ocs_wiredDelta_nonneg N e' t n
  · exact ocs_wiredDelta_tendsto_zero N e' t (hres e' t)
  · 
    intro n e he
    rw [ocs_wiredBulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    rw [edgeIncl_innerEdgeLE]
    exact hres e' t (n - Nat.sqrt n - 1) eb heb
  · 
    intro n e he
    rw [ocs_wiredBulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    rw [SimpleGraph.mem_edgeFinset] at heb
    by_cases hn : 2 ≤ n
    · induction eb with
      | h u v =>
        rw [SimpleGraph.mem_edgeSet] at heb
        exact ocs_wired_bulk_upper N e' t n hn u v heb
    · 
      exfalso
      have hzero : n - Nat.sqrt n - 1 = 0 := by
        have hsq : Nat.sqrt n = 0 ∨ Nat.sqrt n = 1 := by
          interval_cases n <;> simp [Nat.sqrt]
        rcases hsq with h | h <;> rw [h] <;> omega
      induction eb with
      | h u v =>
        rw [SimpleGraph.mem_edgeSet] at heb
        have huv : (u : Site d) = (v : Site d) := by
          have hu := u.2; have hv := v.2
          funext i
          have h1 := hu i; have h2 := hv i
          simp only [mem_box, hzero] at h1 h2; omega
        rw [boxGraph, SimpleGraph.comap_adj] at heb
        change NearestNeighbour d (u : Site d) (v : Site d) at heb
        rw [huv] at heb
        rw [show NearestNeighbour d (v : Site d) (v : Site d)
              ↔ (∑ i, ((v : Site d) i - (v : Site d) i).natAbs) = 1 from Iff.rfl] at heb
        simp at heb
  · 
    have hcard : ∀ n, (ocs_wiredBulkSet d n).card
        = (boxGraph d (n - Nat.sqrt n - 1)).edgeFinset.card :=
      fun n => Finset.card_image_of_injective _ (dfi_innerEdgeLE_injective d _)
    refine (ocs_edgeFinset_shell_fraction_tendsto_zero d hd (fun n => n - Nat.sqrt n - 1)
      (fun n => Nat.sub_le (n - Nat.sqrt n) 1 |>.trans (Nat.sub_le n (Nat.sqrt n)))
      ocs_gap_sub_one_tendsto_zero).congr (fun n => ?_)
    rw [hcard n]


theorem ocs_fk_uniqueness_of_rotation (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hfreeRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_FreeRotationResidue (d := d) N e' t)
    (hwiredRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_WiredRotationResidue (d := d) N e' t) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  bdp_fk_uniqueness_of_offCentreSandwich hd N eb hEbox hg hboxfree
    (ocs_freeOffCentreSandwich_of_rotation hd N hfreeRot)
    (ocs_wiredOffCentreSandwich_of_rotation hd N hwiredRot)

end FK
end StatMech
