/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralShiftDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.IVTranslationInvariance.Part2
import Def.StatisticalMechanics.Code.FK.IntegralShiftDecay.Part2
open MeasureTheory Filter Topology BoundedContinuousFunction
open StatMech.ConfigSpace StatMech.Lattice


namespace StatMech

namespace FK

variable {d : ℕ}


theorem isd_wiredIntegralShiftDecay_of_dense {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hdense : isd_wiredDenseDecay hp hp1 hq g φ) :
    ivt_wiredIntegralShiftDecay hp hp1 hq g φ := by
  obtain ⟨D, hD, hdecay⟩ := hdense
  intro f
  have := isd_tendsto_decay_of_dense
    (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq) g hD hdecay f
  exact this


theorem isd_freeIntegralShiftDecay_of_dense {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hdense : isd_freeDenseDecay hp hp1 hq g φ) :
    ivt_freeIntegralShiftDecay hp hp1 hq g φ := by
  obtain ⟨D, hD, hdecay⟩ := hdense
  intro f
  have := isd_tendsto_decay_of_dense
    (fun n => freeFiniteMeasure d (φ n) hp hp1 hq) g hD hdecay f
  exact this


theorem isd_decayFun_one (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ) (n : ℕ) :
    isd_decayFun μ (1 : Multiplicative (Site d)) f n = 0 := by
  simp only [isd_decayFun, shift_one, id_eq, sub_self]


theorem isd_wiredDenseDecay_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (φ : ℕ → ℕ) : isd_wiredDenseDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
  refine ⟨Set.univ, dense_univ, fun f' _ => ?_⟩
  have hzero : isd_decayFun (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
      (1 : Multiplicative (Site d)) f' = fun _ => (0:ℝ) := by
    funext n; exact isd_decayFun_one _ f' n
  rw [hzero]
  exact tendsto_const_nhds


theorem isd_freeDenseDecay_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (φ : ℕ → ℕ) : isd_freeDenseDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
  refine ⟨Set.univ, dense_univ, fun f' _ => ?_⟩
  have hzero : isd_decayFun (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
      (1 : Multiplicative (Site d)) f' = fun _ => (0:ℝ) := by
    funext n; exact isd_decayFun_one _ f' n
  rw [hzero]
  exact tendsto_const_nhds


theorem isd_wiredIntegralShiftDecay_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (φ : ℕ → ℕ) : ivt_wiredIntegralShiftDecay hp hp1 hq (1 : Multiplicative (Site d)) φ :=
  isd_wiredIntegralShiftDecay_of_dense hp hp1 hq (1 : Multiplicative (Site d)) φ
    (isd_wiredDenseDecay_one hp hp1 hq φ)


theorem isd_wiredIV_isTranslationInvariant_of_denseDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q)
    (hdense : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
          (wiredInfiniteVolume d hp hp1 hq) →
        isd_wiredDenseDecay hp hp1 hq g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) :=
  ivt_wiredIV_isTranslationInvariant_of_decay hp hp1 hq
    (fun g φ hφ hconv => isd_wiredIntegralShiftDecay_of_dense hp hp1 hq g φ
      (hdense g φ hφ hconv))


theorem isd_freeIV_isTranslationInvariant_of_denseDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q)
    (hdense : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
          (freeInfiniteVolume d hp hp1 hq) →
        isd_freeDenseDecay hp hp1 hq g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) :=
  ivt_freeIV_isTranslationInvariant_of_decay hp hp1 hq
    (fun g φ hφ hconv => isd_freeIntegralShiftDecay_of_dense hp hp1 hq g φ
      (hdense g φ hφ hconv))

end FK
end StatMech
