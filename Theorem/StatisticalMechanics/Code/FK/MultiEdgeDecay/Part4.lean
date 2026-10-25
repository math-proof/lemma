/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Theorem.StatisticalMechanics.Code.FK.OffCentreCarrier
import Def.StatisticalMechanics.Code.FK.MultiEdgeDecay.Part4
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


theorem med_wiredMultiHomogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (hplace : med_wiredPlacement hp hp1 g) :
    cdc_wiredMultiHomogeneous hp hp1 g := by
  intro s
  obtain ⟨N, t, t', hst, hst', htrans⟩ := hplace s
  rw [show s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N) from hst', hst]
  exact med_wiredMultiHomogeneous_of_cofinal (Multiplicative.toAdd g) N t t' hp hp1 htrans


theorem med_freeMultiHomogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (hplace : med_freePlacement hp hp1 g) :
    cdc_freeMultiHomogeneous hp hp1 g := by
  intro s
  obtain ⟨N, t, t', hst, hst', htrans⟩ := hplace s
  rw [show s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N) from hst', hst]
  exact med_freeMultiHomogeneous_of_cofinal (Multiplicative.toAdd g) N t t' hp hp1 htrans


theorem med_wiredPlacement_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    med_wiredPlacement hp hp1 (1 : Multiplicative (Site d)) := by
  intro s
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  refine ⟨N, t, t, hst, ?_, ?_⟩
  · rw [hst, Finset.image_image]
    refine Finset.image_congr fun e _ => ?_
    simp only [Function.comp_apply, inv_one, one_smul]
  · refine Filter.Eventually.of_forall fun m hNm => ?_
    exact (med_centred_eq_translated_wired m (Multiplicative.toAdd (1 : Multiplicative (Site d)))
      (t.image (innerEdgeLE d hNm))).symm


theorem med_freePlacement_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    med_freePlacement hp hp1 (1 : Multiplicative (Site d)) := by
  intro s
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  refine ⟨N, t, t, hst, ?_, ?_⟩
  · rw [hst, Finset.image_image]
    refine Finset.image_congr fun e _ => ?_
    simp only [Function.comp_apply, inv_one, one_smul]
  · refine Filter.Eventually.of_forall fun m hNm => ?_
    exact (med_centred_eq_translated_free m (Multiplicative.toAdd (1 : Multiplicative (Site d)))
      (t.image (innerEdgeLE d hNm))).symm


theorem med_wiredMultiHomogeneous_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    cdc_wiredMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) :=
  med_wiredMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) (med_wiredPlacement_one hp hp1)


theorem med_freeMultiHomogeneous_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    cdc_freeMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) :=
  med_freeMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) (med_freePlacement_one hp hp1)


theorem med_wiredIV_isTranslationInvariant_of_placement {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hplace : ∀ g : Multiplicative (Site d), med_wiredPlacement hp hp1 g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  cdc_wiredIV_isTranslationInvariant_of_homogeneous hp hp1
    (fun g _ _ _ => med_wiredMultiHomogeneous hp hp1 g (hplace g))


theorem med_freeIV_isTranslationInvariant_of_placement {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hplace : ∀ g : Multiplicative (Site d), med_freePlacement hp hp1 g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  cdc_freeIV_isTranslationInvariant_of_homogeneous hp hp1
    (fun g _ _ _ => med_freeMultiHomogeneous hp hp1 g (hplace g))

end FK
end StatMech
