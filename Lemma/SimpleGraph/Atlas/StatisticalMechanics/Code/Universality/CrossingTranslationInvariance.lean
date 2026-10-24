import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance
open Set MeasureTheory SimpleGraph StatMech StatMech.Universality


/--
[sym2Congr_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma sym2Congr_apply_eq
  {e : α ≃ β}
  {x : Sym2 α} :
-- imply
  sym2Congr e x = Sym2.map e x := by
-- proof
  apply StatMech.Universality.sym2Congr_apply e x

/--
[cti_edgeEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_edgeEquiv_symm_apply_eq
  {v : Site 2}
  {e : Sym2 (Site 2)} :
-- imply
  (cti_edgeEquiv v).symm e = e.map (· + v) := by
-- proof
  apply StatMech.Universality.cti_edgeEquiv_symm_apply v e

/--
[cti_translateConfig_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_translateConfig_eq_eq
  {v : Site 2} :
-- imply
  translateConfig v = (Equiv.piCongrLeft (fun _ => Bool) (cti_edgeEquiv v)) := by
-- proof
  apply StatMech.Universality.cti_translateConfig_eq v

/--
[cti_measurable_translateConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_measurable_translateConfig_eq
  {v : Site 2} :
-- imply
  Measurable (translateConfig v) := by
-- proof
  apply StatMech.Universality.cti_measurable_translateConfig v

/--
[cti_map_translateConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_map_translateConfig_eq
  {v : Site 2} :
-- imply
  Measure.map (translateConfig v) rba_selfDualMeasure = rba_selfDualMeasure := by
-- proof
  apply StatMech.Universality.cti_map_translateConfig v

/--
[cti_selfDual_shift_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_selfDual_shift_invariant_eq
  {v : Site 2} :
-- imply
  MeasurePreserving (translateConfig v) rba_selfDualMeasure rba_selfDualMeasure := by
-- proof
  apply StatMech.Universality.cti_selfDual_shift_invariant v

/--
[cti_isOpenEdge_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_isOpenEdge_translate_eq
  {t : Site 2}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2} :
-- imply
  IsOpenEdge 2 (translateConfig t ω) x y ↔ IsOpenEdge 2 ω (x + t) (y + t) := by
-- proof
  apply StatMech.Universality.cti_isOpenEdge_translate t ω x y

/--
[cti_mem_rect_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_mem_rect_translate_eq
  {a b c d : ℤ}
  {t : Site 2}
  {x : Site 2} :
-- imply
  x ∈ rect a b c d ↔ (x + t) ∈ rect (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
-- proof
  apply StatMech.Universality.cti_mem_rect_translate a b c d t x

/--
[cti_mem_leftSide_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_mem_leftSide_translate_eq
  {a b c d : ℤ}
  {t : Site 2}
  {x : Site 2} :
-- imply
  x ∈ leftSide a b c d ↔ (x + t) ∈ leftSide (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
-- proof
  apply StatMech.Universality.cti_mem_leftSide_translate a b c d t x

/--
[cti_mem_rightSide_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_mem_rightSide_translate_eq
  {a b c d : ℤ}
  {t : Site 2}
  {x : Site 2} :
-- imply
  x ∈ rightSide a b c d ↔ (x + t) ∈ rightSide (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
-- proof
  apply StatMech.Universality.cti_mem_rightSide_translate a b c d t x

/--
[cti_mem_bottomSide_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_mem_bottomSide_translate_eq
  {a b c d : ℤ}
  {t : Site 2}
  {x : Site 2} :
-- imply
  x ∈ bottomSide a b c d ↔ (x + t) ∈ bottomSide (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
-- proof
  apply StatMech.Universality.cti_mem_bottomSide_translate a b c d t x

/--
[cti_mem_topSide_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_mem_topSide_translate_eq
  {a b c d : ℤ}
  {t : Site 2}
  {x : Site 2} :
-- imply
  x ∈ topSide a b c d ↔ (x + t) ∈ topSide (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
-- proof
  apply StatMech.Universality.cti_mem_topSide_translate a b c d t x

/--
[cti_horizontalCrossing_translate_fwd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_horizontalCrossing_translate_fwd_eq
  {a b c d : ℤ}
  {t : Site 2}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : HorizontalCrossing (translateConfig t ω) a b c d) :
-- imply
  HorizontalCrossing ω (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
-- proof
  apply StatMech.Universality.cti_horizontalCrossing_translate_fwd a b c d t ω h

/--
[cti_horizontalCrossing_translate_bwd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_horizontalCrossing_translate_bwd_eq
  {a b c d : ℤ}
  {t : Site 2}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : HorizontalCrossing ω (a + t 0) (b + t 0) (c + t 1) (d + t 1)) :
-- imply
  HorizontalCrossing (translateConfig t ω) a b c d := by
-- proof
  apply StatMech.Universality.cti_horizontalCrossing_translate_bwd a b c d t ω h

/--
[cti_verticalCrossing_translate_fwd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_verticalCrossing_translate_fwd_eq
  {a b c d : ℤ}
  {t : Site 2}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : VerticalCrossing (translateConfig t ω) a b c d) :
-- imply
  VerticalCrossing ω (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
-- proof
  apply StatMech.Universality.cti_verticalCrossing_translate_fwd a b c d t ω h

/--
[cti_verticalCrossing_translate_bwd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_verticalCrossing_translate_bwd_eq
  {a b c d : ℤ}
  {t : Site 2}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : VerticalCrossing ω (a + t 0) (b + t 0) (c + t 1) (d + t 1)) :
-- imply
  VerticalCrossing (translateConfig t ω) a b c d := by
-- proof
  apply StatMech.Universality.cti_verticalCrossing_translate_bwd a b c d t ω h

/--
[cti_horizontalCrossingEvent_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_horizontalCrossingEvent_translate_eq
  {a b c d : ℤ}
  {t : Site 2} :
-- imply
  horizontalCrossingEvent (a + t 0) (b + t 0) (c + t 1) (d + t 1) = translateConfig t ⁻¹' horizontalCrossingEvent a b c d := by
-- proof
  apply StatMech.Universality.cti_horizontalCrossingEvent_translate a b c d t

/--
[cti_verticalCrossingEvent_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_verticalCrossingEvent_translate_eq
  {a b c d : ℤ}
  {t : Site 2} :
-- imply
  verticalCrossingEvent (a + t 0) (b + t 0) (c + t 1) (d + t 1) = translateConfig t ⁻¹' verticalCrossingEvent a b c d := by
-- proof
  apply StatMech.Universality.cti_verticalCrossingEvent_translate a b c d t

/--
[cti_horizontalCrossing_translation_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_horizontalCrossing_translation_invariant_eq
  {a b c d : ℤ}
  {t : Site 2}
-- given
  (hmeas : MeasurableSet (horizontalCrossingEvent a b c d)) :
-- imply
  rba_selfDualMeasure.real (horizontalCrossingEvent (a + t 0) (b + t 0) (c + t 1) (d + t 1)) = rba_selfDualMeasure.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.cti_horizontalCrossing_translation_invariant a b c d t hmeas

/--
[cti_verticalCrossing_translation_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_verticalCrossing_translation_invariant_eq
  {a b c d : ℤ}
  {t : Site 2}
-- given
  (hmeas : MeasurableSet (verticalCrossingEvent a b c d)) :
-- imply
  rba_selfDualMeasure.real (verticalCrossingEvent (a + t 0) (b + t 0) (c + t 1) (d + t 1)) = rba_selfDualMeasure.real (verticalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.cti_verticalCrossing_translation_invariant a b c d t hmeas

/--
[cti_h2box_discharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_h2box_discharge_eq
  {n : ℤ}
  {γ : ℝ}
  {k : ℕ}
-- given
  (hmeas : MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
  (h2box0 : γ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
  (_hk : 1 ≤ k) :
-- imply
  γ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent (((k : ℤ) - 1) * n) (((k : ℤ) + 1) * n) 0 n) := by
-- proof
  apply StatMech.Universality.cti_h2box_discharge hmeas h2box0 k _hk

/--
[cti_hband_discharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_hband_discharge_eq
  {n : ℤ}
  {k : ℕ}
-- given
  (hmeas : MeasurableSet (verticalCrossingEvent 0 n 0 n))
  (hband0 : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n))
  (_hk : 1 ≤ k) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent (((k : ℤ) - 1) * n) ((k : ℤ) * n) 0 n) := by
-- proof
  apply StatMech.Universality.cti_hband_discharge hmeas hband0 k _hk

/--
[cti_rai_cross_pos_selfDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean)
-/
@[path]
private lemma cti_rai_cross_pos_selfDual_eq
  {n : ℤ}
  {β γ : ℝ}
-- given
  (hpa : PositivelyAssociated rba_selfDualMeasure)
  (hn : 0 < n)
  (hβ : 0 < β)
  (hγ : 0 < γ)
  (hmeas2box : MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
  (hmeasband : MeasurableSet (verticalCrossingEvent 0 n 0 n))
  (hseed : β ≤ rai_cross rba_selfDualMeasure n 1)
  (h2box0 : γ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
  (hband0 : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n)) :
-- imply
  ∀ k : ℕ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧ c ≤ rai_cross rba_selfDualMeasure n k := by
-- proof
  apply StatMech.Universality.cti_rai_cross_pos_selfDual hpa hn hβ hγ hmeas2box hmeasband hseed h2box0 hband0


-- created on 2026-10-23
