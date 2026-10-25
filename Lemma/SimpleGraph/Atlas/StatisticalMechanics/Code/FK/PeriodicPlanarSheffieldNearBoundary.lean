import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldNearBoundary
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNearBoundary.lean)
-/
@[path]
private lemma leftBoundaryExhaustionVertices_mono_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real} :
-- imply
  Monotone (E.leftBoundaryExhaustionVertices r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices_mono E r

/--
[PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNearBoundary.lean)
-/
@[path]
private lemma leftBoundaryExhaustionEvent_mono_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S : Set V} :
-- imply
  Monotone (E.leftBoundaryExhaustionEvent r S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent_mono E r S

/--
[PeriodicPlaneEmbedding.exists_leftBoundaryExhaustion_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNearBoundary.lean)
-/
@[path]
private lemma exists_leftBoundaryExhaustion_subset_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S : Set V}
-- given
  (hSfinite : S.Finite)
  (hSH : S ⊆ E.rightHalfPlaneVertices r) :
-- imply
  ∃ n : Nat, S ⊆ E.leftBoundaryExhaustionVertices r n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_leftBoundaryExhaustion_subset E r hSfinite hSH

/--
[PeriodicPlaneEmbedding.iUnion_leftBoundaryExhaustionEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNearBoundary.lean)
-/
@[path]
private lemma iUnion_leftBoundaryExhaustionEvent_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S : Set V}
-- given
  (hSfinite : S.Finite)
  (hSH : S ⊆ E.rightHalfPlaneVertices r) :
-- imply
  (⋃ n : Nat, E.leftBoundaryExhaustionEvent r S n) = P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iUnion_leftBoundaryExhaustionEvent E r hSfinite hSH

/--
[PeriodicPlaneEmbedding.leftBoundaryExhaustion_measureReal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNearBoundary.lean)
-/
@[path]
private lemma leftBoundaryExhaustion_measureReal_tendsto_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r : Real}
  {S : Set V}
-- given
  (hSfinite : S.Finite)
  (hSH : S ⊆ E.rightHalfPlaneVertices r) :
-- imply
  Tendsto (fun n => mu.real (E.leftBoundaryExhaustionEvent r S n)) atTop (nhds (mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.leftBoundaryExhaustion_measureReal_tendsto E mu r hSfinite hSH

/--
[PeriodicPlaneEmbedding.exists_leftBoundaryExhaustion_measureReal_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNearBoundary.lean)
-/
@[path]
private lemma exists_leftBoundaryExhaustion_measureReal_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
  {S : Set V}
  {epsilon : Real}
-- given
  (hSfinite : S.Finite)
  (hSH : S ⊆ E.rightHalfPlaneVertices r)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ n : Nat, S ⊆ E.leftBoundaryExhaustionVertices r n ∧ mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)) - epsilon < mu.real (E.leftBoundaryExhaustionEvent r S n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_leftBoundaryExhaustion_measureReal_gt E mu r hSfinite hSH hepsilon

/--
[PeriodicPlaneEmbedding.exists_leftBoundaryPlacement_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNearBoundary.lean)
-/
@[path]
private lemma exists_leftBoundaryPlacement_tendsto_one_eq
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
  ∃ source : Nat → Finset V, ∃ radius : Nat → Nat, (∀ N, (source N : Set V) ⊆ E.leftBoundaryExhaustionVertices r (radius N)) ∧ Tendsto (fun N => mu.real (E.leftBoundaryExhaustionEvent r (source N : Set V) (radius N))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_leftBoundaryPlacement_tendsto_one E mu hFKG hTI hunique r

/--
[PeriodicPlaneEmbedding.exists_translatedOrbitBox_leftBoundaryPlacement_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNearBoundary.lean)
-/
@[path]
private lemma exists_translatedOrbitBox_leftBoundaryPlacement_tendsto_one_eq
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
  ∃ base : Nat → Site 2, ∃ radius : Nat → Nat, (∀ N, (P.shift (base N) '' (P.orbitBox N : Set V)) ⊆ E.leftBoundaryExhaustionVertices r (radius N)) ∧ Tendsto (fun N => mu.real (E.leftBoundaryExhaustionEvent r (P.shift (base N) '' (P.orbitBox N : Set V)) (radius N))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_translatedOrbitBox_leftBoundaryPlacement_tendsto_one E mu hFKG hTI hunique r

/--
[PeriodicPlaneEmbedding.exists_buffered_leftBoundaryPlacement_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNearBoundary.lean)
-/
@[path]
private lemma exists_buffered_leftBoundaryPlacement_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {buffer : Nat → Nat}
  {r : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hbuffer : ∀ N, N ≤ buffer N) :
-- imply
  ∃ base : Nat → Site 2, ∃ radius : Nat → Nat, (∀ N, (P.shift (base N) '' (P.orbitBox (buffer N) : Set V)) ⊆ E.leftBoundaryExhaustionVertices r (radius N)) ∧ Tendsto (fun N => mu.real (E.leftBoundaryExhaustionEvent r (P.shift (base N) '' (P.orbitBox N : Set V)) (radius N))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_buffered_leftBoundaryPlacement_tendsto_one E mu hFKG hTI hunique buffer hbuffer r


-- created on 2026-10-23
