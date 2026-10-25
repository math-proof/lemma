import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneInteriorArm
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.exists_opposite_translated_orbitBox_with_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInteriorArm.lean)
-/
@[path]
private lemma exists_opposite_translated_orbitBox_with_margin_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {N : Nat}
  {r R : Real} :
-- imply
  ∃ z₀ z₁ : Site 2, P.shift z₀ '' (P.orbitBox N : Set V) ⊆ E.rightHalfPlaneVertices R ∧ P.shift z₁ '' (P.shift z₀ '' (P.orbitBox N : Set V)) ⊆ (E.rightHalfPlaneVertices r)ᶜ := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_opposite_translated_orbitBox_with_margin E N r R

/--
[PeriodicPlaneEmbedding.exists_finite_infiniteBoundaryConnection_with_margin_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInteriorArm.lean)
-/
@[path]
private lemma exists_finite_infiniteBoundaryConnection_with_margin_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R : Real}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hrR : r ≤ R)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ S : Set V, S.Finite ∧ S ⊆ E.rightHalfPlaneVertices R ∧ 1 - epsilon < mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_finite_infiniteBoundaryConnection_with_margin_gt E mu hFKG hTI hunique hrR hepsilon

/--
[PeriodicPlaneEmbedding.exists_finite_opposite_infiniteBoundaryRays_with_margin_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneInteriorArm.lean)
-/
@[path]
private lemma exists_finite_opposite_infiniteBoundaryRays_with_margin_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R : Real}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hrR : r ≤ R)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ L U : Set V, L.Finite ∧ U.Finite ∧ L ⊆ E.rightHalfPlaneVertices R ∧ U ⊆ E.rightHalfPlaneVertices R ∧ 1 - epsilon < mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) L (E.lowerBoundaryRayVertices r 0)) ∧ 1 - epsilon < mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) U (E.upperBoundaryRayVertices r 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_finite_opposite_infiniteBoundaryRays_with_margin_gt E mu hFKG hTI hunique hrR hepsilon


-- created on 2026-10-23
