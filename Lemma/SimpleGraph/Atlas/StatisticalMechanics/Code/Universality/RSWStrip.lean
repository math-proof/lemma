import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWStrip
open Set MeasureTheory SimpleGraph StatMech StatMech.Universality


/--
[PositivelyAssociated.decreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrip.lean)
-/
@[path]
private lemma decreasing_eq
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {A B : Set (ConfigSpace E)}
-- given
  (hpa : PositivelyAssociated μ)
  (hA : IsDecreasing A)
  (hB : IsDecreasing B)
  (hAm : MeasurableSet A)
  (hBm : MeasurableSet B) :
-- imply
  μ.real A * μ.real B ≤ μ.real (A ∩ B) := by
-- proof
  apply StatMech.Universality.PositivelyAssociated.decreasing μ hpa hA hB hAm hBm

/--
[complUnion_fkg_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrip.lean)
-/
@[path]
private lemma complUnion_fkg_bound_eq
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {A B : Set (ConfigSpace E)}
-- given
  (hpa : PositivelyAssociated μ)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B)
  (hAm : MeasurableSet A)
  (hBm : MeasurableSet B) :
-- imply
  (1 - μ.real A) * (1 - μ.real B) ≤ 1 - μ.real (A ∪ B) := by
-- proof
  apply StatMech.Universality.complUnion_fkg_bound μ hpa hA hB hAm hBm

/--
[sqrt_trick_max_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrip.lean)
-/
@[path]
private lemma sqrt_trick_max_real_eq
  {a b s : ℝ}
-- given
  (ha1 : a ≤ 1)
  (hb1 : b ≤ 1)
  (h : (1 - a) * (1 - b) ≤ 1 - s) :
-- imply
  1 - Real.sqrt (1 - s) ≤ max a b := by
-- proof
  apply StatMech.Universality.sqrt_trick_max_real ha1 hb1 h

/--
[rsw_sqrt_trick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrip.lean)
-/
@[path]
private lemma rsw_sqrt_trick_eq
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {A B : Set (ConfigSpace E)}
-- given
  (hpa : PositivelyAssociated μ)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B)
  (hAm : MeasurableSet A)
  (hBm : MeasurableSet B) :
-- imply
  1 - Real.sqrt (1 - μ.real (A ∪ B)) ≤ max (μ.real A) (μ.real B) := by
-- proof
  apply StatMech.Universality.rsw_sqrt_trick μ hpa hA hB hAm hBm

/--
[rsw_sqrt_trick_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrip.lean)
-/
@[path]
private lemma rsw_sqrt_trick_eq_eq
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {A B : Set (ConfigSpace E)}
-- given
  (hpa : PositivelyAssociated μ)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B)
  (hAm : MeasurableSet A)
  (hBm : MeasurableSet B)
  (hAB : μ.real A = μ.real B) :
-- imply
  1 - Real.sqrt (1 - μ.real (A ∪ B)) ≤ μ.real A := by
-- proof
  apply StatMech.Universality.rsw_sqrt_trick_eq μ hpa hA hB hAm hBm hAB

/--
[hv_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrip.lean)
-/
@[path]
private lemma hv_glue_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a m m' b c d : ℤ}
  {xL : Site 2}
  {p : Site 2}
  {q : Site 2}
  {yR : Site 2}
-- given
  (ham : a ≤ m)
  (hm'b : m' ≤ b)
  (hxL : xL ∈ leftSide a m' c d)
  (hpO : p ∈ rect m m' c d)
  (hpL : p ∈ rect a m' c d)
  (hc1 : ConnectedWithin 2 ω (rect a m' c d) ⟨xL, leftSide_subset hxL⟩ ⟨p, hpL⟩)
  (hqO : q ∈ rect m m' c d)
  (hcV : ConnectedWithin 2 ω (rect m m' c d) ⟨p, hpO⟩ ⟨q, hqO⟩)
  (hyR : yR ∈ rightSide m b c d)
  (hqR : q ∈ rect m b c d)
  (hc2 : ConnectedWithin 2 ω (rect m b c d) ⟨q, hqR⟩ ⟨yR, rightSide_subset hyR⟩) :
-- imply
  HorizontalCrossing ω a b c d := by
-- proof
  apply StatMech.Universality.hv_glue ham hm'b hxL hpO hpL hc1 hqO hcV hyR hqR hc2

/--
[overlapConnectionEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrip.lean)
-/
@[path]
private lemma overlapConnectionEvent_isIncreasing_eq
  {m m' c d : ℤ}
  {p q : Site 2}
-- given
  (hp : p ∈ rect m m' c d)
  (hq : q ∈ rect m m' c d) :
-- imply
  IsIncreasing (overlapConnectionEvent m m' c d p q hp hq) := by
-- proof
  apply StatMech.Universality.overlapConnectionEvent_isIncreasing m m' c d p q hp hq

/--
[hvHalf_glue_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrip.lean)
-/
@[path]
private lemma hvHalf_glue_subset_eq
  {a m m' b c d : ℤ}
  {p q : Site 2}
-- given
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hpO : p ∈ rect m m' c d)
  (hqO : q ∈ rect m m' c d)
  (hpL : p ∈ rect a m' c d)
  (hqR : q ∈ rect m b c d) :
-- imply
  leftHalfCrossingEvent a m' c d p hpL ∩ overlapConnectionEvent m m' c d p q hpO hqO ∩ rightHalfCrossingEvent m b c d q hqR ⊆ horizontalCrossingEvent a b c d := by
-- proof
  apply StatMech.Universality.hvHalf_glue_subset ham hmm' hm'b hpO hqO hpL hqR

/--
[rsw_strip_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrip.lean)
-/
@[path]
private lemma rsw_strip_glue_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {a m m' b c d : ℤ}
  {p q : Site 2}
-- given
  (hpa : PositivelyAssociated μ)
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hpO : p ∈ rect m m' c d)
  (hqO : q ∈ rect m m' c d)
  (hpL : p ∈ rect a m' c d)
  (hqR : q ∈ rect m b c d) :
-- imply
  μ.real (leftHalfCrossingEvent a m' c d p hpL) * μ.real (overlapConnectionEvent m m' c d p q hpO hqO) * μ.real (rightHalfCrossingEvent m b c d q hqR) ≤ μ.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rsw_strip_glue μ hpa ham hmm' hm'b hpO hqO hpL hqR

/--
[rsw_strip_glue_of_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrip.lean)
-/
@[path]
private lemma rsw_strip_glue_of_intersection_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {a m m' b c d : ℤ}
-- given
  (hpa : PositivelyAssociated μ)
  (hint : ∀ ω, HVIntersectionProperty ω a m m' b c d) :
-- imply
  μ.real (horizontalCrossingEvent a m' c d) * μ.real (verticalCrossingEvent m m' c d) * μ.real (horizontalCrossingEvent m b c d) ≤ μ.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rsw_strip_glue_of_intersection μ hpa hint


-- created on 2026-10-23
