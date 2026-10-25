/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Theorem.StatisticalMechanics.Code.FK.OffCentreCarrier
import Def.StatisticalMechanics.Code.FK.MultiEdgeDecay.Part3
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


theorem med_offCentreMultiCarrier_eq_zero (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    (p : ℝ) (m : ℕ) (hNm : N ≤ m) :
    med_offCentreMultiCarrier v N t p m hNm = 0 := by
  unfold med_offCentreMultiCarrier
  rw [← med_centred_eq_translated_wired m v (t.image (innerEdgeLE d hNm)), sub_self]


theorem med_offCentreMultiCarrier_squeeze (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    (p : ℝ) :
    Tendsto (fun m : ℕ => med_offCentreMultiCarrier v N t p (N + m) (Nat.le_add_right N m)) atTop
      (𝓝 0) := by
  have hzero : (fun m : ℕ => med_offCentreMultiCarrier v N t p (N + m) (Nat.le_add_right N m))
      = fun _ => (0:ℝ) := by
    funext m; exact med_offCentreMultiCarrier_eq_zero v N t p (N + m) (Nat.le_add_right N m)
  rw [hzero]
  exact tendsto_const_nhds


theorem med_wiredMultiHomogeneous_of_cofinal (v : Site d) (N : ℕ)
    (t t' : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (htrans : ∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
        med_multiMassProb
            (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2)
            ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))
          = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
              (t'.image (innerEdgeLE d hNm))) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t'.image (edgeIncl d N))) := by
  
  have hCs := med_centred_tendsto_iv N t hp hp1
  
  have hCs' := med_centred_tendsto_iv N t' hp hp1
  
  have heqradius : ∀ᶠ m in atTop,
      (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t.image (edgeIncl d N)))
        = (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (cdc_multiOpenEvent (t'.image (edgeIncl d N))) := by
    filter_upwards [htrans, eventually_ge_atTop N] with m htr hNm
    
    rw [med_centred_mass_lift N m hNm t hp hp1, med_centred_mass_lift N m hNm t' hp hp1]
    
    rw [med_centred_eq_translated_wired m v (t.image (innerEdgeLE d hNm))]
    
    exact htr hNm
  
  have hCs_to_s' : Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t'.image (edgeIncl d N))))) :=
    hCs'.congr' (heqradius.mono fun m h => h.symm)
  exact tendsto_nhds_unique hCs hCs_to_s'


theorem med_freeMultiHomogeneous_of_cofinal (v : Site d) (N : ℕ)
    (t t' : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (htrans : ∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
        med_multiMassProb (fkProb (fvs_transBoxGraph d m v) p 2)
            ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))
          = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm))) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))
      = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t'.image (edgeIncl d N))) := by
  have hCs := med_free_centred_tendsto_iv N t hp hp1
  have hCs' := med_free_centred_tendsto_iv N t' hp hp1
  have heqradius : ∀ᶠ m in atTop,
      (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t.image (edgeIncl d N)))
        = (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (cdc_multiOpenEvent (t'.image (edgeIncl d N))) := by
    filter_upwards [htrans, eventually_ge_atTop N] with m htr hNm
    rw [← med_multiEvent_lift N m hNm t, med_free_centred_mass_eq m (t.image (innerEdgeLE d hNm))
        hp hp1,
      ← med_multiEvent_lift N m hNm t', med_free_centred_mass_eq m (t'.image (innerEdgeLE d hNm))
        hp hp1,
      med_centred_eq_translated_free m v (t.image (innerEdgeLE d hNm))]
    exact htr hNm
  have hCs_to_s' : Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t'.image (edgeIncl d N))))) :=
    hCs'.congr' (heqradius.mono fun m h => h.symm)
  exact tendsto_nhds_unique hCs hCs_to_s'


theorem med_relift_event (N₀ N : ℕ) (h : N₀ ≤ N) (t₀ : Finset (Sym2 (boxVerts d N₀))) :
    cdc_multiOpenEvent ((t₀.image (innerEdgeLE d h)).image (edgeIncl d N))
      = cdc_multiOpenEvent (t₀.image (edgeIncl d N₀)) := by
  congr 1
  rw [Finset.image_image]
  refine Finset.image_congr fun eb _ => ?_
  exact med_edgeIncl_innerEdgeLE N₀ N h eb


end FK
end StatMech
