import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HVIntersection
open Set MeasureTheory SimpleGraph StatMech StatMech.Universality


/--
[hvIntersection_of_meet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HVIntersection.lean)
-/
@[path]
private lemma hvIntersection_of_meet_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a m m' b c d : ℤ}
-- given
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hmeetL : HVMeetProperty ω a m' m m' c d)
  (hmeetR : HVMeetProperty ω m b m m' c d) :
-- imply
  HVIntersectionProperty ω a m m' b c d := by
-- proof
  apply StatMech.Universality.hvIntersection_of_meet ω ham hmm' hm'b hmeetL hmeetR

/--
[hvMeet_of_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HVIntersection.lean)
-/
@[path]
private lemma hvMeet_of_separates_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
-- given
  (hsep : VSeparatesH ω α β m m' c d) :
-- imply
  HVMeetProperty ω α β m m' c d := by
-- proof
  apply StatMech.Universality.hvMeet_of_separates ω α β m m' c d hsep

/--
[hv_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HVIntersection.lean)
-/
@[path]
private lemma hv_intersection_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a m m' b c d : ℤ}
-- given
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hsepL : VSeparatesH ω a m' m m' c d)
  (hsepR : VSeparatesH ω m b m m' c d) :
-- imply
  HVIntersectionProperty ω a m m' b c d := by
-- proof
  apply StatMech.Universality.hv_intersection ω ham hmm' hm'b hsepL hsepR

/--
[rsw_strip_glue_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HVIntersection.lean)
-/
@[path]
private lemma rsw_strip_glue_unconditional_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {a m m' b c d : ℤ}
-- given
  (hpa : PositivelyAssociated μ)
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hsepL : ∀ ω, VSeparatesH ω a m' m m' c d)
  (hsepR : ∀ ω, VSeparatesH ω m b m m' c d) :
-- imply
  μ.real (horizontalCrossingEvent a m' c d) * μ.real (verticalCrossingEvent m m' c d) * μ.real (horizontalCrossingEvent m b c d) ≤ μ.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rsw_strip_glue_unconditional μ hpa ham hmm' hm'b hsepL hsepR


-- created on 2026-10-23
