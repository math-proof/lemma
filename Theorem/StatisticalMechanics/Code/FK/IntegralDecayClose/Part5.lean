/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.IntegralShiftDecay.Part2
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose
import Def.StatisticalMechanics.Code.FK.IntegralDecayClose.Part5
open MeasureTheory Filter Topology BoundedContinuousFunction
open StatMech.ConfigSpace StatMech.Lattice


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


theorem idc_wiredDenseDecay_of_cylinderDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hcyl : idc_wiredCylinderDecay hp hp1 hq g φ) :
    isd_wiredDenseDecay hp hp1 hq g φ :=
  ⟨idc_cylinderBcfSet d, idc_cylinderBcfSet_dense d, hcyl⟩


theorem idc_freeDenseDecay_of_cylinderDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hcyl : idc_freeCylinderDecay hp hp1 hq g φ) :
    isd_freeDenseDecay hp hp1 hq g φ :=
  ⟨idc_cylinderBcfSet d, idc_cylinderBcfSet_dense d, hcyl⟩


theorem idc_wiredIntegralShiftDecay_of_cylinderDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hcyl : idc_wiredCylinderDecay hp hp1 hq g φ) :
    ivt_wiredIntegralShiftDecay hp hp1 hq g φ :=
  isd_wiredIntegralShiftDecay_of_dense hp hp1 hq g φ
    (idc_wiredDenseDecay_of_cylinderDecay hp hp1 hq g φ hcyl)


theorem idc_freeIntegralShiftDecay_of_cylinderDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hcyl : idc_freeCylinderDecay hp hp1 hq g φ) :
    ivt_freeIntegralShiftDecay hp hp1 hq g φ :=
  isd_freeIntegralShiftDecay_of_dense hp hp1 hq g φ
    (idc_freeDenseDecay_of_cylinderDecay hp hp1 hq g φ hcyl)


theorem idc_wiredCylinderDecay_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (φ : ℕ → ℕ) : idc_wiredCylinderDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
  intro f _
  have hzero : isd_decayFun (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
      (1 : Multiplicative (Site d)) f = fun _ => (0 : ℝ) := by
    funext n; exact isd_decayFun_one _ f n
  rw [hzero]
  exact tendsto_const_nhds


theorem idc_freeCylinderDecay_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (φ : ℕ → ℕ) : idc_freeCylinderDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
  intro f _
  have hzero : isd_decayFun (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
      (1 : Multiplicative (Site d)) f = fun _ => (0 : ℝ) := by
    funext n; exact isd_decayFun_one _ f n
  rw [hzero]
  exact tendsto_const_nhds


theorem idc_wiredIntegralShiftDecay_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (φ : ℕ → ℕ) : ivt_wiredIntegralShiftDecay hp hp1 hq (1 : Multiplicative (Site d)) φ :=
  idc_wiredIntegralShiftDecay_of_cylinderDecay hp hp1 hq (1 : Multiplicative (Site d)) φ
    (idc_wiredCylinderDecay_one hp hp1 hq φ)


theorem idc_wiredIV_isTranslationInvariant_of_cylinderDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q)
    (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
          (wiredInfiniteVolume d hp hp1 hq) →
        idc_wiredCylinderDecay hp hp1 hq g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) :=
  isd_wiredIV_isTranslationInvariant_of_denseDecay hp hp1 hq
    (fun g φ hφ hconv => idc_wiredDenseDecay_of_cylinderDecay hp hp1 hq g φ (hcyl g φ hφ hconv))


theorem idc_freeIV_isTranslationInvariant_of_cylinderDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q)
    (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
          (freeInfiniteVolume d hp hp1 hq) →
        idc_freeCylinderDecay hp hp1 hq g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) :=
  isd_freeIV_isTranslationInvariant_of_denseDecay hp hp1 hq
    (fun g φ hφ hconv => idc_freeDenseDecay_of_cylinderDecay hp hp1 hq g φ (hcyl g φ hφ hconv))

end FK
end StatMech
