import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.VSeparatesFixed
open Set MeasureTheory SimpleGraph StatMech StatMech.Universality


/--
[vsFix_hvMeet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/VSeparatesFixed.lean)
-/
@[path]
private lemma vsFix_hvMeet_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
-- given
  (hsep : vsFix_VSeparatesHFixed ω α β m m' c d) :
-- imply
  HVMeetProperty ω α β m m' c d := by
-- proof
  apply StatMech.Universality.vsFix_hvMeet ω α β m m' c d hsep

/--
[vsFix_hvIntersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/VSeparatesFixed.lean)
-/
@[path]
private lemma vsFix_hvIntersection_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a m m' b c d : ℤ}
-- given
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hsepL : vsFix_VSeparatesHFixed ω a m' m m' c d)
  (hsepR : vsFix_VSeparatesHFixed ω m b m m' c d) :
-- imply
  HVIntersectionProperty ω a m m' b c d := by
-- proof
  apply StatMech.Universality.vsFix_hvIntersection ω ham hmm' hm'b hsepL hsepR

/--
[vsFix_rsw_strip_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/VSeparatesFixed.lean)
-/
@[path]
private lemma vsFix_rsw_strip_glue_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {a m m' b c d : ℤ}
-- given
  (hpa : PositivelyAssociated μ)
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hsepL : ∀ ω, vsFix_VSeparatesHFixed ω a m' m m' c d)
  (hsepR : ∀ ω, vsFix_VSeparatesHFixed ω m b m m' c d) :
-- imply
  μ.real (horizontalCrossingEvent a m' c d) * μ.real (verticalCrossingEvent m m' c d) * μ.real (horizontalCrossingEvent m b c d) ≤ μ.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.vsFix_rsw_strip_glue μ hpa ham hmm' hm'b hsepL hsepR

/--
[vsFix_arc_sides_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/VSeparatesFixed.lean)
-/
@[path]
private lemma vsFix_arc_sides_imp_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
-- given
  (harc : vsFix_arc_sides ω α β m m' c d) :
-- imply
  vsFix_VSeparatesHFixed ω α β m m' c d := by
-- proof
  apply StatMech.Universality.vsFix_arc_sides_imp ω α β m m' c d harc

/--
[vsFix_rsw_strip_glue_of_arc_sides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/VSeparatesFixed.lean)
-/
@[path]
private lemma vsFix_rsw_strip_glue_of_arc_sides_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {a m m' b c d : ℤ}
-- given
  (hpa : PositivelyAssociated μ)
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (harcL : ∀ ω, vsFix_arc_sides ω a m' m m' c d)
  (harcR : ∀ ω, vsFix_arc_sides ω m b m m' c d) :
-- imply
  μ.real (horizontalCrossingEvent a m' c d) * μ.real (verticalCrossingEvent m m' c d) * μ.real (horizontalCrossingEvent m b c d) ≤ μ.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.vsFix_rsw_strip_glue_of_arc_sides μ hpa ham hmm' hm'b harcL harcR


-- created on 2026-10-23
