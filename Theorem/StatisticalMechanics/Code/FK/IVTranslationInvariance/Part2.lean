/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVTranslationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKErgodicFull.Part2
import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
import Def.StatisticalMechanics.Code.FK.IVTranslationInvariance
open MeasureTheory Filter Topology BoundedContinuousFunction
open StatMech.ConfigSpace StatMech.Lattice


namespace StatMech

namespace FK

variable {d : ℕ}


theorem ivt_wiredShifted_weakConverges_of_decay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
        (wiredInfiniteVolume d hp hp1 hq))
    (hdecay : ivt_wiredIntegralShiftDecay hp hp1 hq g φ) :
    WeakConvergesTo (fun n => erg_wiredShiftedFinite hp hp1 hq g (φ n))
        (wiredInfiniteVolume d hp hp1 hq) := by
  apply weakConvergesTo_of_forall_tendsto_integral
  intro f
  have hcentred := hconv.tendsto_integral f
  have key :
      Tendsto (fun n => ∫ x, f (shift g x)
          ∂((wiredFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _)) atTop
        (𝓝 (∫ x, f x
          ∂((wiredInfiniteVolume d hp hp1 hq : ProbabilityMeasure _) : Measure _))) := by
    have hsub := hcentred.sub (hdecay f)
    simp only [sub_zero] at hsub
    exact hsub.congr (fun n => by ring)
  exact key.congr (fun n => (ivt_integral_wiredShifted hp hp1 hq g (φ n) f).symm)


theorem ivt_freeShifted_weakConverges_of_decay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
        (freeInfiniteVolume d hp hp1 hq))
    (hdecay : ivt_freeIntegralShiftDecay hp hp1 hq g φ) :
    WeakConvergesTo (fun n => erg_freeShiftedFinite hp hp1 hq g (φ n))
        (freeInfiniteVolume d hp hp1 hq) := by
  apply weakConvergesTo_of_forall_tendsto_integral
  intro f
  have hcentred := hconv.tendsto_integral f
  have key :
      Tendsto (fun n => ∫ x, f (shift g x)
          ∂((freeFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _)) atTop
        (𝓝 (∫ x, f x
          ∂((freeInfiniteVolume d hp hp1 hq : ProbabilityMeasure _) : Measure _))) := by
    have hsub := hcentred.sub (hdecay f)
    simp only [sub_zero] at hsub
    exact hsub.congr (fun n => by ring)
  exact key.congr (fun n => (ivt_integral_freeShifted hp hp1 hq g (φ n) f).symm)


theorem ivt_wiredIV_map_shift_of_decay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d))
    (hdecay : ∀ φ : ℕ → ℕ, StrictMono φ →
        WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
          (wiredInfiniteVolume d hp hp1 hq) →
        ivt_wiredIntegralShiftDecay hp hp1 hq g φ) :
    Measure.map (shift g)
        (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d))))
      = (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) :=
  erg_wiredIV_map_shift hp hp1 hq g
    (fun φ hφ hconv => ivt_wiredShifted_weakConverges_of_decay hp hp1 hq g φ hconv
      (hdecay φ hφ hconv))


theorem ivt_freeIV_map_shift_of_decay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d))
    (hdecay : ∀ φ : ℕ → ℕ, StrictMono φ →
        WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
          (freeInfiniteVolume d hp hp1 hq) →
        ivt_freeIntegralShiftDecay hp hp1 hq g φ) :
    Measure.map (shift g)
        (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d))))
      = (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) :=
  erg_freeIV_map_shift hp hp1 hq g
    (fun φ hφ hconv => ivt_freeShifted_weakConverges_of_decay hp hp1 hq g φ hconv
      (hdecay φ hφ hconv))


theorem ivt_wiredIV_isTranslationInvariant_of_decay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q)
    (hdecay : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
          (wiredInfiniteVolume d hp hp1 hq) →
        ivt_wiredIntegralShiftDecay hp hp1 hq g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro g
  exact ⟨measurable_shift g, ivt_wiredIV_map_shift_of_decay hp hp1 hq g (hdecay g)⟩


theorem ivt_freeIV_isTranslationInvariant_of_decay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q)
    (hdecay : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
          (freeInfiniteVolume d hp hp1 hq) →
        ivt_freeIntegralShiftDecay hp hp1 hq g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro g
  exact ⟨measurable_shift g, ivt_freeIV_map_shift_of_decay hp hp1 hq g (hdecay g)⟩


theorem ivt_wiredIntegralShiftDecay_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (φ : ℕ → ℕ) : ivt_wiredIntegralShiftDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
  intro f
  have hzero : (fun n =>
      (∫ x, f x ∂((wiredFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _))
        - (∫ x, f (shift (1 : Multiplicative (Site d)) x)
            ∂((wiredFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _)))
      = fun _ => (0:ℝ) := by
    funext n
    simp only [shift_one, id_eq, sub_self]
  rw [hzero]
  exact tendsto_const_nhds


theorem ivt_freeIntegralShiftDecay_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (φ : ℕ → ℕ) : ivt_freeIntegralShiftDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
  intro f
  have hzero : (fun n =>
      (∫ x, f x ∂((freeFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _))
        - (∫ x, f (shift (1 : Multiplicative (Site d)) x)
            ∂((freeFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _)))
      = fun _ => (0:ℝ) := by
    funext n
    simp only [shift_one, id_eq, sub_self]
  rw [hzero]
  exact tendsto_const_nhds


theorem ivt_wiredIV_map_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    Measure.map (shift (1 : Multiplicative (Site d)))
        (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d))))
      = (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) :=
  ivt_wiredIV_map_shift_of_decay hp hp1 hq (1 : Multiplicative (Site d))
    (fun φ _ _ => ivt_wiredIntegralShiftDecay_one hp hp1 hq φ)

end FK
end StatMech
