/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Theorem.StatisticalMechanics.Code.FK.OffCentreCarrier
import Def.StatisticalMechanics.Code.FK.MultiEdgeDecay.Part2
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


variable {V : Type*} [Fintype V] [DecidableEq V]


theorem med_centred_mass_eq (m : ℕ) (t : Finset (Sym2 (boxVerts d m))) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d m)))
      = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) t := by
  rw [cdc_multiOpenEvent_image_eq_boxRestrict m t]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' (cdc_boxMultiOpenEvent m t)) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  rw [wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 (cdc_boxMultiOpenEvent m t) hmeas]
  rfl


theorem med_free_centred_mass_eq (m : ℕ) (t : Finset (Sym2 (boxVerts d m))) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d m)))
      = med_multiMassProb (fkProb (boxGraph d m) p 2) t := by
  rw [cdc_multiOpenEvent_image_eq_boxRestrict m t]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' (cdc_boxMultiOpenEvent m t)) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  rw [freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (by norm_num) (cdc_boxMultiOpenEvent m t)
    hmeas]
  rfl


theorem med_centred_eq_translated_wired (m : ℕ) (v : Site d) (t : Finset (Sym2 (boxVerts d m)))
    {p : ℝ} :
    med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) t
      = med_multiMassProb
          (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2)
          (t.image (Sym2.map (fvs_transEquiv d m v))) := by
  unfold med_multiMassProb
  rw [← cdc_eventMassProb_reCfgIso_inv (fvs_transEquiv d m v)
    (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
    (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2)
    (fun ω => fvs_wiredFkProb_reCfgIso (boxGraph d m) (fvs_transBoxGraph d m v)
      (boxBoundary d m) (fvs_transBoxBoundary d m v) (fvs_transEquiv d m v)
      (fvs_transEquiv_adj d m v) (fvs_transEquiv_boundary d m v) p 2 ω)
    (med_genericMultiOpenEvent t)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [med_reCfgIso_preimage (fvs_transEquiv d m v) t]


theorem med_centred_eq_translated_free (m : ℕ) (v : Site d) (t : Finset (Sym2 (boxVerts d m)))
    {p : ℝ} :
    med_multiMassProb (fkProb (boxGraph d m) p 2) t
      = med_multiMassProb
          (fkProb (fvs_transBoxGraph d m v) p 2)
          (t.image (Sym2.map (fvs_transEquiv d m v))) := by
  unfold med_multiMassProb
  rw [← cdc_eventMassProb_reCfgIso_inv (fvs_transEquiv d m v)
    (fkProb (boxGraph d m) p 2)
    (fkProb (fvs_transBoxGraph d m v) p 2)
    (fun ω => fvs_fkProb_reCfgIso (boxGraph d m) (fvs_transBoxGraph d m v)
      (fvs_transEquiv d m v) (fvs_transEquiv_adj d m v) p 2 ω)
    (med_genericMultiOpenEvent t)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [med_reCfgIso_preimage (fvs_transEquiv d m v) t]


theorem med_centred_tendsto_iv (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) :=
  cdc_wired_multiOpenEvent_tendsto N t hp hp1


theorem med_free_centred_tendsto_iv (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) :=
  cdc_free_multiOpenEvent_tendsto N t hp hp1


theorem med_edgeIncl_innerEdgeLE (N m : ℕ) (hNm : N ≤ m) (eb : Sym2 (boxVerts d N)) :
    edgeIncl d m (innerEdgeLE d hNm eb) = edgeIncl d N eb := by
  unfold edgeIncl innerEdgeLE
  rw [Sym2.map_map]
  congr 1


theorem med_multiEvent_lift (N m : ℕ) (hNm : N ≤ m) (t : Finset (Sym2 (boxVerts d N))) :
    cdc_multiOpenEvent ((t.image (innerEdgeLE d hNm)).image (edgeIncl d m))
      = cdc_multiOpenEvent (t.image (edgeIncl d N)) := by
  congr 1
  rw [Finset.image_image]
  refine Finset.image_congr fun eb _ => ?_
  exact med_edgeIncl_innerEdgeLE N m hNm eb


theorem med_centred_mass_lift (N m : ℕ) (hNm : N ≤ m) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))
      = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
          (t.image (innerEdgeLE d hNm)) := by
  rw [← med_multiEvent_lift N m hNm t, med_centred_mass_eq m (t.image (innerEdgeLE d hNm)) hp hp1]


end FK
end StatMech
