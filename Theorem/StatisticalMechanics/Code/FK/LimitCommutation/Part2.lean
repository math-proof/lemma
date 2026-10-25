/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.MultiEdgeDecay.Part4
import Def.StatisticalMechanics.Code.FK.LimitCommutation.Part2
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


theorem lmc_transBoxMass_eq_centred (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (m : ℕ) (hNm : N ≤ m) :
    lmc_transBoxMass v N t p m hNm
      = (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t.image (edgeIncl d N))) := by
  rw [lmc_transBoxMass, med_centred_mass_lift N m hNm t hp hp1,
    ← med_centred_eq_translated_wired m v (t.image (innerEdgeLE d hNm))]


theorem lmc_transBoxMass_tendsto_centred_iv (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m : ℕ => lmc_transBoxMass v N t p (N + m) (Nat.le_add_right N m)) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
  
  have hcentred := (med_centred_tendsto_iv N t hp hp1).comp (tendsto_add_atTop_nat N)
  refine hcentred.congr (fun m => ?_)
  simp only [Function.comp_apply]
  rw [show m + N = N + m from Nat.add_comm m N]
  exact (lmc_transBoxMass_eq_centred v N t hp hp1 (N + m) (Nat.le_add_right N m)).symm


theorem lmc_wiredMultiHomogeneous_of_cofinal (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hcofinal : Tendsto (fun m : ℕ => lmc_transBoxMass v N t p (N + m) (Nat.le_add_right N m))
        atTop
        (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (cdc_multiOpenEvent
                ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e)))))) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent
              ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e))) :=
  tendsto_nhds_unique (lmc_transBoxMass_tendsto_centred_iv v N t hp hp1) hcofinal


theorem lmc_wiredMultiHomogeneous_of_decay (v : Site d) (N N' : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) (t' : Finset (Sym2 (boxVerts d N')))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hst' : (t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e)
        = t'.image (edgeIncl d N'))
    (hdecay : Tendsto
        (fun m : ℕ => lmc_transBoxMass v N t p (N + m) (Nat.le_add_right N m)
          - (wiredFiniteMeasure d (N' + m) hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real
                (cdc_multiOpenEvent (t'.image (edgeIncl d N')))) atTop (𝓝 0)) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent
              ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e))) := by
  rw [hst']
  
  have hC := lmc_transBoxMass_tendsto_centred_iv v N t hp hp1
  
  have hC' := (med_centred_tendsto_iv N' t' hp hp1).comp (tendsto_add_atTop_nat N')
  
  
  have hsum : Tendsto (fun m : ℕ => lmc_transBoxMass v N t p (N + m) (Nat.le_add_right N m)) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t'.image (edgeIncl d N'))))) := by
    have hcomb := hdecay.add hC'
    simp only [zero_add] at hcomb
    refine hcomb.congr (fun m => ?_)
    simp only [Function.comp_apply]
    rw [show m + N' = N' + m from Nat.add_comm m N', sub_add_cancel]
  exact tendsto_nhds_unique hC hsum


end FK
end StatMech
