/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.MultiEdgeDecay.Part4
import Def.StatisticalMechanics.Code.FK.LimitCommutation.Part4
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}


theorem lmc_transBoxMassFree_eq_centred (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (m : ℕ) (hNm : N ≤ m) :
    lmc_transBoxMassFree v N t p m hNm
      = (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t.image (edgeIncl d N))) := by
  rw [lmc_transBoxMassFree, ← med_multiEvent_lift N m hNm t,
    med_free_centred_mass_eq m (t.image (innerEdgeLE d hNm)) hp hp1,
    ← med_centred_eq_translated_free m v (t.image (innerEdgeLE d hNm))]


theorem lmc_transBoxMassFree_tendsto_centred_iv (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m : ℕ => lmc_transBoxMassFree v N t p (N + m) (Nat.le_add_right N m)) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
  have hcentred := (med_free_centred_tendsto_iv N t hp hp1).comp (tendsto_add_atTop_nat N)
  refine hcentred.congr (fun m => ?_)
  simp only [Function.comp_apply]
  rw [show m + N = N + m from Nat.add_comm m N]
  exact (lmc_transBoxMassFree_eq_centred v N t hp hp1 (N + m) (Nat.le_add_right N m)).symm


theorem lmc_freeMultiHomogeneous_of_cofinal (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hcofinal : Tendsto (fun m : ℕ => lmc_transBoxMassFree v N t p (N + m) (Nat.le_add_right N m))
        atTop
        (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (cdc_multiOpenEvent
                ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e)))))) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))
      = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent
              ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e))) :=
  tendsto_nhds_unique (lmc_transBoxMassFree_tendsto_centred_iv v N t hp hp1) hcofinal


end FK
end StatMech
