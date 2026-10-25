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
import Def.StatisticalMechanics.Code.FK.OffCentreSandwichProof.Part3
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


theorem ocs_free_bulk_lower (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (u v : boxVerts d (n - Nat.sqrt n)) (hadj : (boxGraph d (n - Nat.sqrt n)).Adj u v) :
    freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - ocs_freeDelta N e' t n
      ≤ edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2)
          (innerEdgeLE d (Nat.sub_le n (Nat.sqrt n)) (s(u, v) : Sym2 (boxVerts d (n - Nat.sqrt n)))) := by
  have hR : 1 ≤ Nat.sqrt n := by rw [Nat.one_le_iff_ne_zero, Ne, Nat.sqrt_eq_zero]; omega
  have hRn : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  have hmn : n - Nat.sqrt n ≤ n := Nat.sub_le n (Nat.sqrt n)
  obtain ⟨p0, hp0⟩ := ocs_edge_dir_candMap d (n - Nat.sqrt n) u v hadj
  have c0 := ocs_zero_mem_box d (Nat.sqrt n)
  have cw : ((v : Site d) - (u : Site d)) ∈ box d (Nat.sqrt n) := by
    rw [hp0]; exact ocs_candMap_mem_box d (Nat.sqrt n) hR p0
  have hlow := ocs_free_offCentre_lower d (Nat.sqrt n) n hRn hmn u v
    (fsc_logistic_pos t) (fsc_logistic_lt_one t) c0 cw
  have hue : (s((⟨(0 : Site d), c0⟩ : boxVerts d (Nat.sqrt n)),
        (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d (Nat.sqrt n))))
      = ocs_unitEdge d (Nat.sqrt n) hR p0 := by
    unfold ocs_unitEdge; congr 1; exact Subtype.ext hp0
  rw [hue] at hlow
  have hmarg : ocs_unitMarg d n p0 t
      = edgeMargProb (fkProb (boxGraph d (Nat.sqrt n)) (fsc_logistic t) 2)
          (ocs_unitEdge d (Nat.sqrt n) hR p0) := by
    unfold ocs_unitMarg; rw [dif_pos hR]
  have hterm : |freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - ocs_unitMarg d n p0 t|
      ≤ ocs_freeDelta N e' t n :=
    Finset.single_le_sum
      (f := fun p => |freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - ocs_unitMarg d n p t|)
      (fun p _ => abs_nonneg _) (Finset.mem_univ p0)
  have h1 : freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - ocs_freeDelta N e' t n
      ≤ ocs_unitMarg d n p0 t := by
    have h2 : freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - ocs_unitMarg d n p0 t
        ≤ ocs_freeDelta N e' t n := le_trans (le_abs_self _) hterm
    linarith
  rw [hmarg] at h1
  exact le_trans h1 hlow

set_option maxHeartbeats 2000000 in


theorem ocs_freeOffCentreSandwich_of_rotation (hd : 1 ≤ d) (N : ℕ)
    (hres : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_FreeRotationResidue (d := d) N e' t) :
    bdp_FreeOffCentreSandwich (d := d) N := by
  intro e' t
  refine ⟨ocs_bulkSet d, ocs_freeDelta N e' t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro n e he
    rw [ocs_bulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    exact ocs_innerEdgeLE_mem_edgeFinset d _ eb heb
  · exact fun n => ocs_freeDelta_nonneg N e' t n
  · exact ocs_freeDelta_tendsto_zero N e' t (hres e' t)
  · 
    intro n e he
    rw [ocs_bulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    rw [edgeIncl_innerEdgeLE]
    exact hres e' t (n - Nat.sqrt n) eb heb
  · 
    intro n e he
    rw [ocs_bulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    rw [SimpleGraph.mem_edgeFinset] at heb
    by_cases hn : 1 ≤ n
    · induction eb with
      | h u v =>
        rw [SimpleGraph.mem_edgeSet] at heb
        exact ocs_free_bulk_lower N e' t n hn u v heb
    · 
      exfalso
      have hn0 : n = 0 := by omega
      subst hn0
      induction eb with
      | h u v =>
        rw [SimpleGraph.mem_edgeSet] at heb
        have huv : (u : Site d) = (v : Site d) := by
          have hu := u.2; have hv := v.2
          funext i
          have h1 := hu i; have h2 := hv i
          simp only [Nat.zero_sub, mem_box] at h1 h2; omega
        rw [boxGraph, SimpleGraph.comap_adj] at heb
        change NearestNeighbour d (u : Site d) (v : Site d) at heb
        rw [huv] at heb
        rw [show NearestNeighbour d (v : Site d) (v : Site d)
              ↔ (∑ i, ((v : Site d) i - (v : Site d) i).natAbs) = 1 from Iff.rfl] at heb
        simp at heb
  · 
    have hcard : ∀ n, (ocs_bulkSet d n).card = (boxGraph d (n - Nat.sqrt n)).edgeFinset.card :=
      fun n => Finset.card_image_of_injective _
        (dfi_innerEdgeLE_injective d (Nat.sub_le n (Nat.sqrt n)))
    refine (ocs_edgeFinset_shell_fraction_tendsto_zero d hd (fun n => n - Nat.sqrt n)
      (fun n => Nat.sub_le n _) ocs_gap_sub_tendsto_zero).congr (fun n => ?_)
    rw [hcard n]


set_option maxHeartbeats 1500000 in

theorem ocs_unitEdge_wired_marg_tendsto (d : ℕ) (p : Fin d × Bool) {pr : ℝ}
    (hp : 0 < pr) (hp1 : pr < 1) :
    Tendsto (fun n =>
        if hR : 1 ≤ Nat.sqrt n then
          edgeMargProb (wiredFkProb (boxGraph d (Nat.sqrt n)) (boxBoundary d (Nat.sqrt n)) pr 2)
            (ocs_unitEdge d (Nat.sqrt n) hR p)
        else (0 : ℝ)) atTop
      (𝓝 (wiredEdgeDensity d 2 (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) p)) pr)) := by
  have hbase := dfi_wired_density_eq_limit 1 (ocs_unitEdge d 1 (le_refl 1) p) hp hp1
  have hmap : Tendsto (fun n : ℕ => Nat.sqrt n - 1) atTop atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    refine ⟨(b + 1) * (b + 1), fun n hn => ?_⟩
    have : b + 1 ≤ Nat.sqrt n := by
      calc b + 1 = Nat.sqrt ((b + 1) * (b + 1)) := (Nat.sqrt_eq (b + 1)).symm
        _ ≤ Nat.sqrt n := Nat.sqrt_le_sqrt hn
    omega
  have hcomp := hbase.comp hmap
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hR : 1 ≤ Nat.sqrt n := by rw [Nat.one_le_iff_ne_zero, Ne, Nat.sqrt_eq_zero]; omega
  simp only [Function.comp_apply, dif_pos hR]
  have hrr : 1 + (Nat.sqrt n - 1) = Nat.sqrt n := Nat.add_sub_cancel' hR
  rw [ocs_unitEdge_eq_innerEdgeLE d (Nat.sqrt n) hR p]
  exact congrArg (fun s : {s : ℕ // 1 ≤ s} =>
    edgeMargProb (wiredFkProb (boxGraph d s.1) (boxBoundary d s.1) pr 2)
      (innerEdgeLE d s.2 (ocs_unitEdge d 1 (le_refl 1) p)))
    (show (⟨1 + (Nat.sqrt n - 1), Nat.le_add_right 1 _⟩ : {s : ℕ // 1 ≤ s}) = ⟨Nat.sqrt n, hR⟩ from
      Subtype.ext hrr)


end FK
end StatMech
