import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldOpenBoundarySource
open Filter MeasureTheory Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_measureReal_ge_sq_of_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundarySource.lean)
-/
@[path]
private lemma infiniteOpenBoundaryConnection_measureReal_ge_sq_of_translate_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
  {S : Set V}
  {z : Site 2}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hS : S ⊆ E.rightHalfPlaneVertices r)
  (hT : P.shift z '' S ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
-- imply
  (mu.real (P.setHitsInfinite S)) ^ 2 ≤ mu.real (E.infiniteOpenBoundaryConnection r S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_measureReal_ge_sq_of_translate E mu hFKG hTI hunique r S z hS hT

/--
[PeriodicPlaneEmbedding.exists_infiniteOpenBoundaryConnection_ge_orbitBox_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundarySource.lean)
-/
@[path]
private lemma exists_infiniteOpenBoundaryConnection_ge_orbitBox_sq_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
  {N : Nat}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  ∃ S : Set V, S ⊆ E.rightHalfPlaneVertices r ∧ (mu.real (P.orbitBoxHitsInfinite N)) ^ 2 ≤ mu.real (E.infiniteOpenBoundaryConnection r S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_infiniteOpenBoundaryConnection_ge_orbitBox_sq E mu hFKG hTI hunique r N

/--
[PeriodicPlaneEmbedding.exists_infiniteOpenBoundaryConnection_sequence_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundarySource.lean)
-/
@[path]
private lemma exists_infiniteOpenBoundaryConnection_sequence_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  ∃ S : Nat → Set V, (∀ N, S N ⊆ E.rightHalfPlaneVertices r) ∧ Tendsto (fun N => mu.real (E.infiniteOpenBoundaryConnection r (S N))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_infiniteOpenBoundaryConnection_sequence_tendsto_one E mu hFKG hTI hunique r

/--
[PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_lower_union_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundarySource.lean)
-/
@[path]
private lemma infiniteOpenBoundaryConnectionTo_lower_union_upper_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r s : Real}
  {S : Set V} :
-- imply
  E.infiniteOpenBoundaryConnectionTo r S (E.lowerBoundaryRayVertices r s) ∪ E.infiniteOpenBoundaryConnectionTo r S (E.upperBoundaryRayVertices r s) = E.infiniteOpenBoundaryConnection r S := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_lower_union_upper E r s S

/--
[PeriodicPlaneEmbedding.exists_infiniteOpenBoundaryRay_max_sequence_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundarySource.lean)
-/
@[path]
private lemma exists_infiniteOpenBoundaryRay_max_sequence_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
  {s : Nat → Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  ∃ S : Nat → Set V, (∀ N, S N ⊆ E.rightHalfPlaneVertices r) ∧ Tendsto (fun N => max (mu.real (E.infiniteOpenBoundaryConnectionTo r (S N) (E.lowerBoundaryRayVertices r (s N)))) (mu.real (E.infiniteOpenBoundaryConnectionTo r (S N) (E.upperBoundaryRayVertices r (s N))))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_infiniteOpenBoundaryRay_max_sequence_tendsto_one E mu hFKG hTI hunique r s


-- created on 2026-10-23
