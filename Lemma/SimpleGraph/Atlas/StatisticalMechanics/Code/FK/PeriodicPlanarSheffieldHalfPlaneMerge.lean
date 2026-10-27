import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneMerge
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.halfPlanePairMergeErrorUnion_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneMerge.lean)
-/
@[path]
private lemma halfPlanePairMergeErrorUnion_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : ℝ}
  {L R : Finset V} :
-- imply
  MeasurableSet (E.halfPlanePairMergeErrorUnion r L R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.halfPlanePairMergeErrorUnion_measurableSet E r L R

/--
[PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeErrorUnion_preimage_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneMerge.lean)
-/
@[path]
private lemma exists_shift_halfPlanePairMergeErrorUnion_preimage_subset_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {N : ℕ}
  {r : ℝ}
  {L R : Finset V} :
-- imply
  ∃ z : Site 2, P.configTranslate z ⁻¹' E.halfPlanePairMergeErrorUnion r (L.image (P.shift z)) (R.image (P.shift z)) ⊆ P.pairMergeErrorUnion L R N := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeErrorUnion_preimage_subset E N r L R

/--
[PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeErrorUnion_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneMerge.lean)
-/
@[path]
private lemma exists_shift_halfPlanePairMergeErrorUnion_measureReal_le_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {N : ℕ}
  {r : ℝ}
  {L R : Finset V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  ∃ z : Site 2, mu.real (E.halfPlanePairMergeErrorUnion r (L.image (P.shift z)) (R.image (P.shift z))) ≤ mu.real (P.pairMergeErrorUnion L R N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeErrorUnion_measureReal_le E mu hTI N r L R

/--
[PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeErrorUnion_measureReal_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneMerge.lean)
-/
@[path]
private lemma exists_shift_halfPlanePairMergeErrorUnion_measureReal_lt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : ℝ}
  {L R : Finset V}
  {ε : ℝ}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hε : 0 < ε) :
-- imply
  ∃ z : Site 2, mu.real (E.halfPlanePairMergeErrorUnion r (L.image (P.shift z)) (R.image (P.shift z))) < ε := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeErrorUnion_measureReal_lt E mu hTI hunique r L R hε

/--
[PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeErrorUnion_measureReal_le_with_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneMerge.lean)
-/
@[path]
private lemma exists_shift_halfPlanePairMergeErrorUnion_measureReal_le_with_sources_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {N : Nat}
  {r : Real}
  {L R : Finset V}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hLR : ∀ v ∈ L ∪ R, v ∈ P.orbitBox (P.bufferedRadius N)) :
-- imply
  ∃ z : Site 2, (L.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices r ∧ (R.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices r ∧ mu.real (E.halfPlanePairMergeErrorUnion r (L.image (P.shift z)) (R.image (P.shift z))) ≤ mu.real (P.pairMergeErrorUnion L R N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeErrorUnion_measureReal_le_with_sources E mu hTI N r L R hLR

/--
[PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeErrorUnion_measureReal_le_with_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneMerge.lean)
-/
@[path]
private lemma exists_shift_halfPlanePairMergeErrorUnion_measureReal_le_with_margin_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {N : Nat}
  {r R : Real}
  {L Rset : Finset V}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hrR : r ≤ R)
  (hLR : ∀ v ∈ L ∪ Rset, v ∈ P.orbitBox (P.bufferedRadius N)) :
-- imply
  ∃ z : Site 2, (L.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices R ∧ (Rset.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices R ∧ mu.real (E.halfPlanePairMergeErrorUnion r (L.image (P.shift z)) (Rset.image (P.shift z))) ≤ mu.real (P.pairMergeErrorUnion L Rset N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeErrorUnion_measureReal_le_with_margin E mu hTI N hrR L Rset hLR


-- created on 2026-10-23
