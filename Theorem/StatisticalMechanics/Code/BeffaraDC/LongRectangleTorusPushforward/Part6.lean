/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover.Part6
import Theorem.StatisticalMechanics.Code.FK.FKG
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part5
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.Universality


theorem torusAmbientConfigExtend_translate
    (L : ℕ) [Fact (2 < L)] (t : Site 2)
    (omega : TorusAmbientConfig L) :
    torusAmbientConfigExtend L (torusAmbientTranslateConfig L t omega) =
      FK.reCfgIso (torusSiteTranslateEquiv L t)
        (torusAmbientConfigExtend L omega) := by
  funext e
  by_cases he : e ∈ (onsTorusGraph L).edgeFinset
  · have hte : Sym2.map (torusSiteTranslateEquiv L t) e ∈
        (onsTorusGraph L).edgeFinset :=
      (torusSiteTranslate_mem_edgeFinset_iff L t e).2 he
    rw [torusAmbientConfigExtend, dif_pos he, torusAmbientTranslateConfig,
      FK.fvs_reCfgIso_apply, torusAmbientConfigExtend, dif_pos hte]
    rfl
  · have hte : Sym2.map (torusSiteTranslateEquiv L t) e ∉
        (onsTorusGraph L).edgeFinset := by
      intro h
      exact he ((torusSiteTranslate_mem_edgeFinset_iff L t e).1 h)
    rw [torusAmbientConfigExtend, dif_neg he, FK.fvs_reCfgIso_apply,
      torusAmbientConfigExtend, dif_neg hte]


theorem torusPlanarPullback_translate
    (L : ℕ) [Fact (2 < L)] (t : Site 2)
    (omega : TorusAmbientConfig L) :
    torusPlanarPullback L (torusAmbientTranslateConfig L t omega) =
      translateConfig t (torusPlanarPullback L omega) := by
  funext e
  unfold torusPlanarPullback translateConfig
  rw [torusAmbientConfigExtend_translate, FK.fvs_reCfgIso_apply,
    Sym2.map_map]
  change torusAmbientConfigExtend L omega
      (Sym2.map (torusSiteTranslateEquiv L t ∘ torusReduceSite L) e) =
    torusAmbientConfigExtend L omega
      (Sym2.map (torusReduceSite L)
        (Sym2.map (fun x => x + t) e))
  rw [Sym2.map_map]
  congr 1
  apply Sym2.map_congr
  intro z _hz
  exact (torusReduceSite_add L z t).symm


theorem measurable_torusAmbientTranslateConfig
    (L : ℕ) [Fact (2 < L)] (t : Site 2) :
    Measurable (torusAmbientTranslateConfig L t) :=
  measurable_of_finite _


theorem torusAmbientFKWeight_translate
    (L : ℕ) [Fact (2 < L)] (t : Site 2)
    (p q : ℝ) (omega : TorusAmbientConfig L) :
    torusAmbientFKWeight L p q
        (torusAmbientTranslateConfig L t omega) =
      torusAmbientFKWeight L p q omega := by
  unfold torusAmbientFKWeight
  rw [torusAmbientConfigExtend_translate]
  exact FK.fvs_fkWeight_reCfgIso (onsTorusGraph L) (onsTorusGraph L)
    (torusSiteTranslateEquiv L t)
    (fun x y => (onsTorusGraph_adj_translate L t x y).symm)
    p q (torusAmbientConfigExtend L omega)


theorem torusAmbientProbability_translate
    (L : ℕ) [Fact (2 < L)] (t : Site 2)
    (p q : ℝ) (omega : TorusAmbientConfig L) :
    torusAmbientProbability L p q
        (torusAmbientTranslateConfig L t omega) =
      torusAmbientProbability L p q omega := by
  unfold torusAmbientProbability
  rw [torusAmbientFKWeight_translate]


theorem torusAmbientTranslateConfig_measurePreserving
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (t : Site 2) :
    MeasurePreserving (torusAmbientTranslateConfig L t)
      (torusAmbientMeasure L hp hp1 hq)
      (torusAmbientMeasure L hp hp1 hq) := by
  refine ⟨measurable_torusAmbientTranslateConfig L t, ?_⟩
  apply Measure.ext_of_singleton
  intro omega
  rw [Measure.map_apply (measurable_torusAmbientTranslateConfig L t)
    (measurableSet_singleton omega)]
  have hpre : torusAmbientTranslateConfig L t ⁻¹' {omega} =
      {(torusAmbientTranslateConfigEquiv L t).symm omega} := by
    ext eta
    simp only [mem_preimage, mem_singleton_iff]
    change (torusAmbientTranslateConfigEquiv L t) eta = omega ↔ _
    constructor
    · intro h
      rw [← h, Equiv.symm_apply_apply]
    · intro h
      rw [h, Equiv.apply_symm_apply]
  rw [hpre, torusAmbientMeasure_singleton,
    torusAmbientMeasure_singleton]
  congr 1
  calc
    torusAmbientProbability L p q
        ((torusAmbientTranslateConfigEquiv L t).symm omega) =
      torusAmbientProbability L p q
        (torusAmbientTranslateConfig L t
          ((torusAmbientTranslateConfigEquiv L t).symm omega)) :=
        (torusAmbientProbability_translate L t p q _).symm
    _ = torusAmbientProbability L p q omega := by
      change torusAmbientProbability L p q
        ((torusAmbientTranslateConfigEquiv L t)
          ((torusAmbientTranslateConfigEquiv L t).symm omega)) = _
      rw [Equiv.apply_symm_apply]


theorem torusPlanarPushforward_shiftInvariant_of_torus
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (t : Site 2)
    (hshift : MeasurePreserving (torusAmbientTranslateConfig L t)
      (torusAmbientMeasure L hp hp1 hq)
      (torusAmbientMeasure L hp hp1 hq)) :
    MeasurePreserving (translateConfig t)
      (torusPlanarPushforward L hp hp1 hq)
      (torusPlanarPushforward L hp hp1 hq) := by
  refine ⟨cti_measurable_translateConfig t, ?_⟩
  unfold torusPlanarPushforward
  rw [Measure.map_map (cti_measurable_translateConfig t)
    (measurable_torusPlanarPullback L)]
  have hcomp : translateConfig t ∘ torusPlanarPullback L =
      torusPlanarPullback L ∘ torusAmbientTranslateConfig L t := by
    funext omega
    exact (torusPlanarPullback_translate L t omega).symm
  rw [hcomp]
  rw [← Measure.map_map (measurable_torusPlanarPullback L)
    (measurable_torusAmbientTranslateConfig L t)]
  rw [hshift.map_eq]


theorem torusPlanarPushforward_allShiftInvariant_of_torus
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hshift : ∀ t : Site 2,
      MeasurePreserving (torusAmbientTranslateConfig L t)
        (torusAmbientMeasure L hp hp1 hq)
        (torusAmbientMeasure L hp hp1 hq)) :
    ∀ t : Site 2, MeasurePreserving (translateConfig t)
      (torusPlanarPushforward L hp hp1 hq)
      (torusPlanarPushforward L hp hp1 hq) := by
  intro t
  exact torusPlanarPushforward_shiftInvariant_of_torus
    L hp hp1 hq t (hshift t)


theorem torusPlanarPushforward_allShiftInvariant
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∀ t : Site 2, MeasurePreserving (translateConfig t)
      (torusPlanarPushforward L hp hp1 hq)
      (torusPlanarPushforward L hp hp1 hq) := by
  exact torusPlanarPushforward_allShiftInvariant_of_torus L hp hp1 hq
    (torusAmbientTranslateConfig_measurePreserving L hp hp1 hq)


theorem bdcLongRectangle_polynomial_deficit_of_torusCover
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq : 1 ≤ q)
    {alpha n : ℕ} (ha : 0 < alpha) (hn : 1 ≤ n)
    (W : Set (TorusAmbientConfig L))
    (hcover : BdcTorusWindingToThinCover L alpha n W)
    {c epsilon : ℝ} (hc : 0 ≤ c)
    (hW : 1 - (torusAmbientMeasure L hp hp1 hq0).real W ≤
      c * (n : ℝ) ^ (-epsilon)) :
    1 - c ^ ((1 : ℝ) / (2 * alpha ^ 3 : ℕ)) *
        (n : ℝ) ^ (-epsilon / (2 * alpha ^ 3 : ℕ)) ≤
      (torusPlanarPushforward L hp hp1 hq0).real
        (bdcLongRectangleBaseEvent alpha n) := by
  apply bdcLongRectangle_polynomial_deficit_of_cover
    (torusPlanarPushforward L hp hp1 hq0)
    (torusPlanarPushforward_positivelyAssociated_of_one_le
      L hp hp1 hq0 hq)
    (torusPlanarPushforward_allShiftInvariant L hp hp1 hq0)
    ha hn (bdcTorusPlanarLiftEvent L W)
    hcover.planarLift_subset_longRectangleUnion hc
  simpa only [torusPlanarPushforward_real_planarLiftEvent_apply]
    using hW

end StatMech.BeffaraDC
