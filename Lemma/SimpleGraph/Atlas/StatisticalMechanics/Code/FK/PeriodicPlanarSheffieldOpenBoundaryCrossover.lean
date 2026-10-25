import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldOpenBoundaryCrossover
open Filter MeasureTheory Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.exists_adjacent_infiniteOpenBoundaryRays_measureReal_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundaryCrossover.lean)
-/
@[path]
private lemma exists_adjacent_infiniteOpenBoundaryRays_measureReal_ge_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r s : Real}
  {S : Set V}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ z : Int, 1 - Real.sqrt (1 - mu.real (E.infiniteOpenBoundaryConnection r S)) - epsilon ≤ mu.real (E.infiniteOpenBoundaryConnectionTo r (P.shift (verticalShift z) '' S) (E.lowerBoundaryRayVertices r s)) ∧ 1 - Real.sqrt (1 - mu.real (E.infiniteOpenBoundaryConnection r S)) - epsilon ≤ mu.real (E.infiniteOpenBoundaryConnectionTo r (P.shift (verticalShift (z + 1)) '' S) (E.upperBoundaryRayVertices r s)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_adjacent_infiniteOpenBoundaryRays_measureReal_ge E mu hFKG hTI r s S hepsilon

/--
[PeriodicPlaneEmbedding.exists_separated_infiniteOpenBoundaryRays_measureReal_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundaryCrossover.lean)
-/
@[path]
private lemma exists_separated_infiniteOpenBoundaryRays_measureReal_ge_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r s : Real}
  {t : Int}
  {S : Set V}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ z : Int, 1 - Real.sqrt (1 - mu.real (E.infiniteOpenBoundaryConnection r S)) - epsilon ≤ mu.real (E.infiniteOpenBoundaryConnectionTo r (P.shift (verticalShift z) '' S) (E.lowerBoundaryRayVertices r s)) ∧ 1 - Real.sqrt (1 - mu.real (E.infiniteOpenBoundaryConnection r S)) - epsilon ≤ mu.real (E.infiniteOpenBoundaryConnectionTo r (P.shift (verticalShift (z + 1 + t)) '' S) (E.upperBoundaryRayVertices r (s + t))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_separated_infiniteOpenBoundaryRays_measureReal_ge E mu hFKG hTI r s t S hepsilon


-- created on 2026-10-23
