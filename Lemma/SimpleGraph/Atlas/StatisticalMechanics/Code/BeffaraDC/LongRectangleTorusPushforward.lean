import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward
open MeasureTheory Set StatMech StatMech.BeffaraDC


/--
[torusAmbientPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusAmbientPMF_apply_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {omega : TorusAmbientConfig L}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  torusAmbientPMF L hp hp1 hq omega = ENNReal.ofReal (torusAmbientProbability L p q omega) := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientPMF_apply L hp hp1 hq omega

/--
[torusAmbientMeasure_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusAmbientMeasure_singleton_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {omega : TorusAmbientConfig L}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  torusAmbientMeasure L hp hp1 hq {omega} = ENNReal.ofReal (torusAmbientProbability L p q omega) := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientMeasure_singleton L hp hp1 hq omega

/--
[torusAmbientProbability_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusAmbientProbability_nonneg_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {omega : TorusAmbientConfig L}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 ≤ torusAmbientProbability L p q omega := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientProbability_nonneg L hp hp1 hq omega

/--
[torusAmbientMeasure_real_eq_indicator_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusAmbientMeasure_real_eq_indicator_sum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {A : Set (TorusAmbientConfig L)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (torusAmbientMeasure L hp hp1 hq).real A = ∑ omega : TorusAmbientConfig L, torusAmbientProbability L p q omega * A.indicator (fun _ => (1 : ℝ)) omega := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientMeasure_real_eq_indicator_sum L hp hp1 hq A

/--
[torusAmbientConfigExtend_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusAmbientConfigExtend_sup_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega eta : TorusAmbientConfig L} :
-- imply
  torusAmbientConfigExtend L (omega ⊔ eta) = torusAmbientConfigExtend L omega ⊔ torusAmbientConfigExtend L eta := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientConfigExtend_sup L omega eta

/--
[torusAmbientConfigExtend_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusAmbientConfigExtend_inf_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega eta : TorusAmbientConfig L} :
-- imply
  torusAmbientConfigExtend L (omega ⊓ eta) = torusAmbientConfigExtend L omega ⊓ torusAmbientConfigExtend L eta := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientConfigExtend_inf L omega eta

/--
[torusAmbientFKWeight_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusAmbientFKWeight_logSupermodular_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {omega eta : TorusAmbientConfig L}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  torusAmbientFKWeight L p q omega * torusAmbientFKWeight L p q eta ≤ torusAmbientFKWeight L p q (omega ⊔ eta) * torusAmbientFKWeight L p q (omega ⊓ eta) := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientFKWeight_logSupermodular L hp hp1 hq omega eta

/--
[torusAmbientProbability_FKGLatticeCondition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusAmbientProbability_FKGLatticeCondition_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  FKGLatticeCondition (torusAmbientProbability L p q) := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientProbability_FKGLatticeCondition L hp hp1 hq

/--
[torusAmbientMeasure_positivelyAssociated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusAmbientMeasure_positivelyAssociated_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq0 : 0 < q)
  (hq : 1 ≤ q) :
-- imply
  PositivelyAssociated (torusAmbientMeasure L hp hp1 hq0) := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientMeasure_positivelyAssociated L hp hp1 hq0 hq

/--
[measurable_torusPlanarPullback](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma measurable_torusPlanarPullback_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Measurable (torusPlanarPullback L) := by
-- proof
  apply StatMech.BeffaraDC.measurable_torusPlanarPullback L

/--
[measurableEmbedding_torusPlanarPullback](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma measurableEmbedding_torusPlanarPullback_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  MeasurableEmbedding (torusPlanarPullback L) := by
-- proof
  apply StatMech.BeffaraDC.measurableEmbedding_torusPlanarPullback L

/--
[torusPlanarPushforward_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusPlanarPushforward_apply_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {B : Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  torusPlanarPushforward L hp hp1 hq B = torusAmbientMeasure L hp hp1 hq (torusPlanarPullback L ⁻¹' B) := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPushforward_apply L hp hp1 hq B

/--
[torusPlanarPushforward_real_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusPlanarPushforward_real_apply_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {B : Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (torusPlanarPushforward L hp hp1 hq).real B = (torusAmbientMeasure L hp hp1 hq).real (torusPlanarPullback L ⁻¹' B) := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPushforward_real_apply L hp hp1 hq B

/--
[torusPlanarPushforward_image_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusPlanarPushforward_image_apply_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {A : Set (TorusAmbientConfig L)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  torusPlanarPushforward L hp hp1 hq (torusPlanarPullback L '' A) = torusAmbientMeasure L hp hp1 hq A := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPushforward_image_apply L hp hp1 hq A

/--
[torusPlanarPushforward_real_image_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusPlanarPushforward_real_image_apply_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {A : Set (TorusAmbientConfig L)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (torusPlanarPushforward L hp hp1 hq).real (torusPlanarPullback L '' A) = (torusAmbientMeasure L hp hp1 hq).real A := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPushforward_real_image_apply L hp hp1 hq A

/--
[torusPlanarPushforward_planarLiftEvent_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusPlanarPushforward_planarLiftEvent_apply_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {A : Set (TorusAmbientConfig L)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  torusPlanarPushforward L hp hp1 hq (bdcTorusPlanarLiftEvent L A) = torusAmbientMeasure L hp hp1 hq A := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPushforward_planarLiftEvent_apply L hp hp1 hq A

/--
[torusPlanarPushforward_real_planarLiftEvent_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusPlanarPushforward_real_planarLiftEvent_apply_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {A : Set (TorusAmbientConfig L)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (torusPlanarPushforward L hp hp1 hq).real (bdcTorusPlanarLiftEvent L A) = (torusAmbientMeasure L hp hp1 hq).real A := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPushforward_real_planarLiftEvent_apply L hp hp1 hq A

/--
[monotone_torusPlanarPullback](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma monotone_torusPlanarPullback_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Monotone (torusPlanarPullback L) := by
-- proof
  apply StatMech.BeffaraDC.monotone_torusPlanarPullback L

/--
[torusPlanarPullback_preimage_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusPlanarPullback_preimage_isIncreasing_eq
  {L : ℕ}
  [Fact (2 < L)]
  {A : Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hA : IsIncreasing A) :
-- imply
  IsIncreasing (torusPlanarPullback L ⁻¹' A) := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPullback_preimage_isIncreasing L hA

/--
[torusPlanarPushforward_positivelyAssociated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusPlanarPushforward_positivelyAssociated_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hpa : PositivelyAssociated (torusAmbientMeasure L hp hp1 hq)) :
-- imply
  PositivelyAssociated (torusPlanarPushforward L hp hp1 hq) := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPushforward_positivelyAssociated L hp hp1 hq hpa

/--
[torusPlanarPushforward_positivelyAssociated_of_one_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusPlanarPushforward_positivelyAssociated_of_one_le_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq0 : 0 < q)
  (hq : 1 ≤ q) :
-- imply
  PositivelyAssociated (torusPlanarPushforward L hp hp1 hq0) := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPushforward_positivelyAssociated_of_one_le L hp hp1 hq0 hq

/--
[torusSiteTranslateEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusSiteTranslateEquiv_apply_eq
  {L : ℕ}
  {t : Site 2}
  {z : ZMod L × ZMod L} :
-- imply
  torusSiteTranslateEquiv L t z = (z.1 + (t 0 : ZMod L), z.2 + (t 1 : ZMod L)) := by
-- proof
  apply StatMech.BeffaraDC.torusSiteTranslateEquiv_apply L t z

/--
[torusReduceSite_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusReduceSite_add_eq
  {L : ℕ}
  {z t : Site 2} :
-- imply
  torusReduceSite L (z + t) = torusSiteTranslateEquiv L t (torusReduceSite L z) := by
-- proof
  apply StatMech.BeffaraDC.torusReduceSite_add L z t

/--
[onsTorusGraph_adj_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma onsTorusGraph_adj_translate_eq
  {L : ℕ}
  [Fact (2 < L)]
  {t : Site 2}
  {x y : ZMod L × ZMod L} :
-- imply
  (onsTorusGraph L).Adj (torusSiteTranslateEquiv L t x) (torusSiteTranslateEquiv L t y) ↔ (onsTorusGraph L).Adj x y := by
-- proof
  apply StatMech.BeffaraDC.onsTorusGraph_adj_translate L t x y

/--
[torusSiteTranslate_mem_edgeFinset_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusSiteTranslate_mem_edgeFinset_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {t : Site 2}
  {e : Sym2 (ZMod L × ZMod L)} :
-- imply
  Sym2.map (torusSiteTranslateEquiv L t) e ∈ (onsTorusGraph L).edgeFinset ↔ e ∈ (onsTorusGraph L).edgeFinset := by
-- proof
  apply StatMech.BeffaraDC.torusSiteTranslate_mem_edgeFinset_iff L t e

/--
[torusAmbientConfigExtend_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusAmbientConfigExtend_translate_eq
  {L : ℕ}
  [Fact (2 < L)]
  {t : Site 2}
  {omega : TorusAmbientConfig L} :
-- imply
  torusAmbientConfigExtend L (torusAmbientTranslateConfig L t omega) = FK.reCfgIso (torusSiteTranslateEquiv L t) (torusAmbientConfigExtend L omega) := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientConfigExtend_translate L t omega

/--
[torusPlanarPullback_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusPlanarPullback_translate_eq
  {L : ℕ}
  [Fact (2 < L)]
  {t : Site 2}
  {omega : TorusAmbientConfig L} :
-- imply
  torusPlanarPullback L (torusAmbientTranslateConfig L t omega) = translateConfig t (torusPlanarPullback L omega) := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPullback_translate L t omega

/--
[measurable_torusAmbientTranslateConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma measurable_torusAmbientTranslateConfig_eq
  {L : ℕ}
  [Fact (2 < L)]
  {t : Site 2} :
-- imply
  Measurable (torusAmbientTranslateConfig L t) := by
-- proof
  apply StatMech.BeffaraDC.measurable_torusAmbientTranslateConfig L t

/--
[torusAmbientFKWeight_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusAmbientFKWeight_translate_eq
  {L : ℕ}
  [Fact (2 < L)]
  {t : Site 2}
  {p q : ℝ}
  {omega : TorusAmbientConfig L} :
-- imply
  torusAmbientFKWeight L p q (torusAmbientTranslateConfig L t omega) = torusAmbientFKWeight L p q omega := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientFKWeight_translate L t p q omega

/--
[torusAmbientProbability_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusAmbientProbability_translate_eq
  {L : ℕ}
  [Fact (2 < L)]
  {t : Site 2}
  {p q : ℝ}
  {omega : TorusAmbientConfig L} :
-- imply
  torusAmbientProbability L p q (torusAmbientTranslateConfig L t omega) = torusAmbientProbability L p q omega := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientProbability_translate L t p q omega

/--
[torusAmbientTranslateConfig_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusAmbientTranslateConfig_measurePreserving_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {t : Site 2}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  MeasurePreserving (torusAmbientTranslateConfig L t) (torusAmbientMeasure L hp hp1 hq) (torusAmbientMeasure L hp hp1 hq) := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientTranslateConfig_measurePreserving L hp hp1 hq t

/--
[torusPlanarPushforward_shiftInvariant_of_torus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusPlanarPushforward_shiftInvariant_of_torus_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {t : Site 2}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hshift : MeasurePreserving (torusAmbientTranslateConfig L t) (torusAmbientMeasure L hp hp1 hq) (torusAmbientMeasure L hp hp1 hq)) :
-- imply
  MeasurePreserving (translateConfig t) (torusPlanarPushforward L hp hp1 hq) (torusPlanarPushforward L hp hp1 hq) := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPushforward_shiftInvariant_of_torus L hp hp1 hq t hshift

/--
[torusPlanarPushforward_allShiftInvariant_of_torus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusPlanarPushforward_allShiftInvariant_of_torus_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hshift : ∀ t : Site 2, MeasurePreserving (torusAmbientTranslateConfig L t) (torusAmbientMeasure L hp hp1 hq) (torusAmbientMeasure L hp hp1 hq)) :
-- imply
  ∀ t : Site 2, MeasurePreserving (translateConfig t) (torusPlanarPushforward L hp hp1 hq) (torusPlanarPushforward L hp hp1 hq) := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPushforward_allShiftInvariant_of_torus L hp hp1 hq hshift

/--
[torusPlanarPushforward_allShiftInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma torusPlanarPushforward_allShiftInvariant_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∀ t : Site 2, MeasurePreserving (translateConfig t) (torusPlanarPushforward L hp hp1 hq) (torusPlanarPushforward L hp hp1 hq) := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPushforward_allShiftInvariant L hp hp1 hq

/--
[bdcLongRectangle_polynomial_deficit_of_torusCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean)
-/
@[path]
private lemma bdcLongRectangle_polynomial_deficit_of_torusCover_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {alpha n : ℕ}
  {W : Set (TorusAmbientConfig L)}
  {c epsilon : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq0 : 0 < q)
  (hq : 1 ≤ q)
  (ha : 0 < alpha)
  (hn : 1 ≤ n)
  (hcover : BdcTorusWindingToThinCover L alpha n W)
  (hc : 0 ≤ c)
  (hW : 1 - (torusAmbientMeasure L hp hp1 hq0).real W ≤ c * (n : ℝ) ^ (-epsilon)) :
-- imply
  1 - c ^ ((1 : ℝ) / (2 * alpha ^ 3 : ℕ)) * (n : ℝ) ^ (-epsilon / (2 * alpha ^ 3 : ℕ)) ≤ (torusPlanarPushforward L hp hp1 hq0).real (bdcLongRectangleBaseEvent alpha n) := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangle_polynomial_deficit_of_torusCover L hp hp1 hq0 hq ha hn W hcover hc hW


-- created on 2026-10-23
