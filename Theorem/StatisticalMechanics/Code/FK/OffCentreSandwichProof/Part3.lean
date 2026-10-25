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
import Def.StatisticalMechanics.Code.FK.OffCentreSandwichProof.Part2
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


theorem ocs_freeDelta_nonneg (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ) (n : ℕ) :
    0 ≤ ocs_freeDelta N e' t n :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)


theorem ocs_perDir_tendsto_zero (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hres : ocs_FreeRotationResidue (d := d) N e' t) (p : Fin d × Bool) :
    Tendsto (fun n => |freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)
        - ocs_unitMarg d n p t|) atTop (𝓝 0) := by
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  have hconv := ocs_unitEdge_marg_tendsto d p hp hp1
  have hLeq : freeEdgeDensity d 2 (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) p)) (fsc_logistic t)
      = freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) :=
    hres 1 (ocs_unitEdge d 1 (le_refl 1) p) (ocs_unitEdge1_mem_edgeFinset d p)
  rw [hLeq] at hconv
  have hmt : Tendsto (fun n => ocs_unitMarg d n p t) atTop
      (𝓝 (freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t))) := hconv.congr (fun n => rfl)
  have hsub := (tendsto_const_nhds
    (x := freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t))).sub hmt
  rw [sub_self] at hsub
  have := hsub.abs
  rwa [abs_zero] at this


theorem ocs_freeDelta_tendsto_zero (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hres : ocs_FreeRotationResidue (d := d) N e' t) :
    Tendsto (fun n => ocs_freeDelta N e' t n) atTop (𝓝 0) := by
  have h : Tendsto (fun n => ∑ p : Fin d × Bool,
      |freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - ocs_unitMarg d n p t|)
      atTop (𝓝 (∑ p : Fin d × Bool, (0 : ℝ))) :=
    tendsto_finset_sum _ (fun p _ => ocs_perDir_tendsto_zero N e' t hres p)
  rw [Finset.sum_const_zero] at h
  exact h


theorem ocs_innerEdgeLE_mem_edgeFinset (d : ℕ) {m n : ℕ} (h : m ≤ n) (eb : Sym2 (boxVerts d m))
    (heb : eb ∈ (boxGraph d m).edgeFinset) :
    innerEdgeLE d h eb ∈ (boxGraph d n).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset] at heb ⊢
  induction eb with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj] at heb
    rw [innerEdgeLE, Sym2.map_mk, SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj]
    exact heb


end FK
end StatMech
