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
import Def.StatisticalMechanics.Code.FK.OffCentreSandwichProof
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


theorem ocs_unitEdge_eq_innerEdgeLE (d r : ℕ) (hr : 1 ≤ r) (p : Fin d × Bool) :
    ocs_unitEdge d r hr p = innerEdgeLE d hr (ocs_unitEdge d 1 (le_refl 1) p) := by
  unfold ocs_unitEdge innerEdgeLE
  rw [Sym2.map_mk]; congr 1


theorem ocs_unitEdge1_mem_edgeFinset (d : ℕ) (p : Fin d × Bool) :
    ocs_unitEdge d 1 (le_refl 1) p ∈ (boxGraph d 1).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  show (boxGraph d 1).Adj _ _
  rw [boxGraph, SimpleGraph.comap_adj]
  show NearestNeighbour d (0 : Site d) (candMap d (0 : Site d) p)
  exact adj_candMap d (0 : Site d) p

set_option maxHeartbeats 1500000 in


theorem ocs_unitEdge_marg_tendsto (d : ℕ) (p : Fin d × Bool) {pr : ℝ} (hp : 0 < pr) (hp1 : pr < 1) :
    Tendsto (fun n =>
        if hR : 1 ≤ Nat.sqrt n then
          edgeMargProb (fkProb (boxGraph d (Nat.sqrt n)) pr 2) (ocs_unitEdge d (Nat.sqrt n) hR p)
        else (0 : ℝ)) atTop
      (𝓝 (freeEdgeDensity d 2 (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) p)) pr)) := by
  have hbase := dfi_free_density_eq_limit 1 (ocs_unitEdge d 1 (le_refl 1) p) hp hp1
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
    edgeMargProb (fkProb (boxGraph d s.1) pr 2) (innerEdgeLE d s.2 (ocs_unitEdge d 1 (le_refl 1) p)))
    (show (⟨1 + (Nat.sqrt n - 1), Nat.le_add_right 1 _⟩ : {s : ℕ // 1 ≤ s}) = ⟨Nat.sqrt n, hR⟩ from
      Subtype.ext hrr)


end FK
end StatMech
