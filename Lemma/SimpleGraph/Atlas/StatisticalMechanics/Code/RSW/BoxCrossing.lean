import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.RSW.BoxCrossing
open Set MeasureTheory StatMech StatMech.RSW StatMech.RSW.BoxCrossing


/--
[sqrt_trick_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossing.lean)
-/
@[path]
private lemma sqrt_trick_real_eq
  {m s : ℝ}
-- given
  (hm1 : m ≤ 1)
  (h : (1 - m) ^ 2 ≤ 1 - s) :
-- imply
  1 - Real.sqrt (1 - s) ≤ m := by
-- proof
  apply StatMech.RSW.BoxCrossing.sqrt_trick_real hm1 h

/--
[complFKG_union_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossing.lean)
-/
@[path]
private lemma complFKG_union_bound_eq
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {A B : Set (ConfigSpace E)}
-- given
  (hA : MeasurableSet A)
  (hB : MeasurableSet B)
  (hFKGc : μ.real Aᶜ * μ.real Bᶜ ≤ μ.real (Aᶜ ∩ Bᶜ)) :
-- imply
  μ.real Aᶜ * μ.real Bᶜ ≤ 1 - μ.real (A ∪ B) := by
-- proof
  apply StatMech.RSW.BoxCrossing.complFKG_union_bound μ hA hB hFKGc

/--
[sqrt_trick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossing.lean)
-/
@[path]
private lemma sqrt_trick_eq
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {A B : Set (ConfigSpace E)}
-- given
  (hA : MeasurableSet A)
  (hB : MeasurableSet B)
  (hm : μ.real A = μ.real B)
  (hFKGc : μ.real Aᶜ * μ.real Bᶜ ≤ μ.real (Aᶜ ∩ Bᶜ)) :
-- imply
  1 - Real.sqrt (1 - μ.real (A ∪ B)) ≤ μ.real A := by
-- proof
  apply StatMech.RSW.BoxCrossing.sqrt_trick μ hA hB hm hFKGc

/--
[square_crossing_ge_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossing.lean)
-/
@[path]
private lemma square_crossing_ge_half_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {n : ℤ}
-- given
  (hdualExists : (squareCrossingEvent n)ᶜ ⊆ squareDualCrossingEvent n)
  (hselfDual : μ.real (squareDualCrossingEvent n) = μ.real (squareCrossingEvent n))
  (hmeas : MeasurableSet (squareCrossingEvent n)) :
-- imply
  (1 : ℝ) / 2 ≤ μ.real (squareCrossingEvent n) := by
-- proof
  apply StatMech.RSW.BoxCrossing.square_crossing_ge_half μ n hdualExists hselfDual hmeas

/--
[rect_glue_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossing.lean)
-/
@[path]
private lemma rect_glue_subset_eq
  {n : ℤ}
  {z : Site 2}
-- given
  (hn : 0 ≤ n)
  (hz0 : z 0 = n)
  (hzc : 0 ≤ z 1)
  (hzd : z 1 ≤ n) :
-- imply
  rectLeftHalfEvent n hn hz0 hzc hzd ∩ rectRightHalfEvent n hn hz0 hzc hzd ⊆ rectangleCrossingEvent n := by
-- proof
  apply StatMech.RSW.BoxCrossing.rect_glue_subset n hn hz0 hzc hzd

/--
[measureReal_rectangleCrossing_ge_halves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossing.lean)
-/
@[path]
private lemma measureReal_rectangleCrossing_ge_halves_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsFiniteMeasure μ]
  {n : ℤ}
  {z : Site 2}
-- given
  (hpa : PositivelyAssociated μ)
  (hn : 0 ≤ n)
  (hz0 : z 0 = n)
  (hzc : 0 ≤ z 1)
  (hzd : z 1 ≤ n) :
-- imply
  μ.real (rectLeftHalfEvent n hn hz0 hzc hzd) * μ.real (rectRightHalfEvent n hn hz0 hzc hzd) ≤ μ.real (rectangleCrossingEvent n) := by
-- proof
  apply StatMech.RSW.BoxCrossing.measureReal_rectangleCrossing_ge_halves μ hpa n hn hz0 hzc hzd

/--
[box_crossing_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossing.lean)
-/
@[path]
private lemma box_crossing_lower_bound_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {n : ℤ}
  {z : Site 2}
-- given
  (hpa : PositivelyAssociated μ)
  (hn : 0 ≤ n)
  (hz0 : z 0 = n)
  (hzc : 0 ≤ z 1)
  (hzd : z 1 ≤ n)
  (hrouteLeft : (1 : ℝ) / 2 ≤ μ.real (rectLeftHalfEvent n hn hz0 hzc hzd))
  (hrouteRight : (1 : ℝ) / 2 ≤ μ.real (rectRightHalfEvent n hn hz0 hzc hzd)) :
-- imply
  (1 : ℝ) / 4 ≤ μ.real (rectangleCrossingEvent n) := by
-- proof
  apply StatMech.RSW.BoxCrossing.box_crossing_lower_bound μ hpa n hn hz0 hzc hzd hrouteLeft hrouteRight

/--
[box_crossing_lower_bound_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossing.lean)
-/
@[path]
private lemma box_crossing_lower_bound_pos_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {n : ℤ}
  {z : Site 2}
-- given
  (hpa : PositivelyAssociated μ)
  (hn : 0 ≤ n)
  (hz0 : z 0 = n)
  (hzc : 0 ≤ z 1)
  (hzd : z 1 ≤ n)
  (hrouteLeft : (1 : ℝ) / 2 ≤ μ.real (rectLeftHalfEvent n hn hz0 hzc hzd))
  (hrouteRight : (1 : ℝ) / 2 ≤ μ.real (rectRightHalfEvent n hn hz0 hzc hzd)) :
-- imply
  ∃ c : ℝ, 0 < c ∧ c ≤ μ.real (rectangleCrossingEvent n) := by
-- proof
  apply StatMech.RSW.BoxCrossing.box_crossing_lower_bound_pos μ hpa n hn hz0 hzc hzd hrouteLeft hrouteRight


-- created on 2026-10-23
