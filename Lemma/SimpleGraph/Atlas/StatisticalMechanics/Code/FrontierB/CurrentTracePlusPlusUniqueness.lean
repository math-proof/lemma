import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.CurrentTracePlusPlusUniqueness
open MeasureTheory StatMech StatMech.FrontierB


/--
[plusPlusSuperposedTraceLaw_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTracePlusPlusUniqueness.lean)
-/
@[path]
private lemma plusPlusSuperposedTraceLaw_uniqueness_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 ≤ beta)
  (hd : 1 ≤ d) :
-- imply
  let mu := (independentSuperposedTraceLaw (infinitePlusCurrentMeasure d beta hbeta) (infinitePlusCurrentMeasure d beta hbeta) : Measure (ConfigSpace (Sym2 (Site d)))) (mu {omega | numInfiniteClusters d omega = 0} = 1 ∨ mu {omega | numInfiniteClusters d omega = 1} = 1) ∧ mu (atLeastTwoInfinite d) = 0 ∧ mu {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierB.plusPlusSuperposedTraceLaw_uniqueness d beta hbeta hd


-- created on 2026-10-23
