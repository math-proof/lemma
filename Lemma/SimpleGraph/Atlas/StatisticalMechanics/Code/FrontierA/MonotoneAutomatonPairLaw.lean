import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonPairLaw.Part3
open MeasureTheory StatMech StatMech.FrontierA


/--
[pairSiteLeft_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean)
-/
@[path]
private lemma pairSiteLeft_pair_eq
  {d : ℕ}
  {eta zeta : ConfigSpace (Site d)} :
-- imply
  pairSiteLeft (pairSiteConfig eta zeta) = eta := by
-- proof
  apply StatMech.FrontierA.pairSiteLeft_pair eta zeta

/--
[pairSiteRight_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean)
-/
@[path]
private lemma pairSiteRight_pair_eq
  {d : ℕ}
  {eta zeta : ConfigSpace (Site d)} :
-- imply
  pairSiteRight (pairSiteConfig eta zeta) = zeta := by
-- proof
  apply StatMech.FrontierA.pairSiteRight_pair eta zeta

/--
[measurable_pairSiteConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean)
-/
@[path]
private lemma measurable_pairSiteConfig_eq
  {d : ℕ} :
-- imply
  Measurable (Function.uncurry pairSiteConfig : (ConfigSpace (Site d) × ConfigSpace (Site d)) → PairSiteConfig d) := by
-- proof
  apply StatMech.FrontierA.measurable_pairSiteConfig

/--
[measurable_pairSiteLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean)
-/
@[path]
private lemma measurable_pairSiteLeft_eq
  {d : ℕ} :
-- imply
  Measurable (pairSiteLeft : PairSiteConfig d → ConfigSpace (Site d)) := by
-- proof
  apply StatMech.FrontierA.measurable_pairSiteLeft

/--
[measurable_pairSiteRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean)
-/
@[path]
private lemma measurable_pairSiteRight_eq
  {d : ℕ} :
-- imply
  Measurable (pairSiteRight : PairSiteConfig d → ConfigSpace (Site d)) := by
-- proof
  apply StatMech.FrontierA.measurable_pairSiteRight

/--
[pairSiteConfig_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean)
-/
@[path]
private lemma pairSiteConfig_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {eta zeta : ConfigSpace (Site d)} :
-- imply
  pairSiteConfig (shift g eta) (shift g zeta) = shift g (pairSiteConfig eta zeta) := by
-- proof
  apply StatMech.FrontierA.pairSiteConfig_shift g eta zeta

/--
[pairSiteLeft_interpolatedHighPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean)
-/
@[path]
private lemma pairSiteLeft_interpolatedHighPair_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {q : FieldTriple d} :
-- imply
  pairSiteLeft (interpolatedHighPair T q) = interpolatedSite T q := by
-- proof
  apply StatMech.FrontierA.pairSiteLeft_interpolatedHighPair T q

/--
[pairSiteRight_interpolatedHighPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean)
-/
@[path]
private lemma pairSiteRight_interpolatedHighPair_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {q : FieldTriple d} :
-- imply
  pairSiteRight (interpolatedHighPair T q) = T q.2.2 := by
-- proof
  apply StatMech.FrontierA.pairSiteRight_interpolatedHighPair T q

/--
[measurable_interpolatedHighPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean)
-/
@[path]
private lemma measurable_interpolatedHighPair_eq
  {d : ℕ}
  {T : MonotoneAutomaton d} :
-- imply
  Measurable (interpolatedHighPair T : FieldTriple d → PairSiteConfig d) := by
-- proof
  apply StatMech.FrontierA.measurable_interpolatedHighPair T

/--
[interpolatedHighPair_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean)
-/
@[path]
private lemma interpolatedHighPair_shift_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {g : Multiplicative (Site d)}
  {q : FieldTriple d} :
-- imply
  interpolatedHighPair T (tripleFieldShift g q) = shift g (interpolatedHighPair T q) := by
-- proof
  apply StatMech.FrontierA.interpolatedHighPair_shift T g q

/--
[interpolatedHighPairLaw_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean)
-/
@[path]
private lemma interpolatedHighPairLaw_isTranslationInvariant_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
-- given
  (hinv : IsTripleFieldTranslationInvariant mu) :
-- imply
  IsTranslationInvariant (G := Multiplicative (Site d)) (interpolatedHighPairLaw T mu) := by
-- proof
  apply StatMech.FrontierA.interpolatedHighPairLaw_isTranslationInvariant T mu hinv

/--
[interpolatedHighPair_nested](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean)
-/
@[path]
private lemma interpolatedHighPair_nested_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {q : FieldTriple d}
-- given
  (hq : IsMonotoneFieldTriple q) :
-- imply
  pairSiteLeft (interpolatedHighPair T q) ≤ pairSiteRight (interpolatedHighPair T q) := by
-- proof
  apply StatMech.FrontierA.interpolatedHighPair_nested T q hq


-- created on 2026-10-23
