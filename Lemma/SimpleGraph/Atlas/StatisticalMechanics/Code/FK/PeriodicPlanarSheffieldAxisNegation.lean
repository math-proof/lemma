import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisNegation.Part2
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[siteNeg_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisNegation.lean)
-/
@[path]
private lemma siteNeg_zero_eq
  [DecidableEq V]
  [Countable V] :
-- imply
  siteNeg (0 : Site 2) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.siteNeg_zero

/--
[siteNeg_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisNegation.lean)
-/
@[path]
private lemma siteNeg_add_eq
  [DecidableEq V]
  [Countable V]
  {z w : Site 2} :
-- imply
  siteNeg (z + w) = siteNeg z + siteNeg w := by
-- proof
  apply StatMech.FK.PeriodicPlanar.siteNeg_add z w

/--
[siteNeg_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisNegation.lean)
-/
@[path]
private lemma siteNeg_neg_eq
  [DecidableEq V]
  [Countable V]
  {z : Site 2} :
-- imply
  siteNeg (siteNeg z) = z := by
-- proof
  apply StatMech.FK.PeriodicPlanar.siteNeg_neg z

/--
[PeriodicPlaneEmbedding.axisNeg_vertexCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisNegation.lean)
-/
@[path]
private lemma axisNeg_vertexCoord_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {x : V}
  {i : Fin 2} :
-- imply
  E.axisNeg.vertexCoord x i = -E.vertexCoord x i := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisNeg_vertexCoord E x i

/--
[PeriodicGraph.axisNeg_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisNegation.lean)
-/
@[path]
private lemma axisNeg_isTranslationInvariant_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  P.axisNeg.IsTranslationInvariant mu := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.axisNeg_isTranslationInvariant P mu hTI

/--
[PeriodicGraph.axisNeg_orbitBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisNegation.lean)
-/
@[path]
private lemma axisNeg_orbitBox_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {n : Nat} :
-- imply
  P.axisNeg.orbitBox n = P.orbitBox n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.axisNeg_orbitBox P n

/--
[PeriodicPlaneEmbedding.axisNeg_rectVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisNegation.lean)
-/
@[path]
private lemma axisNeg_rectVertices_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real} :
-- imply
  E.axisNeg.rectVertices a b c d = E.rectVertices (-b) (-a) (-d) (-c) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisNeg_rectVertices E a b c d

/--
[PeriodicPlaneEmbedding.axisNeg_leftBoundaryVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisNegation.lean)
-/
@[path]
private lemma axisNeg_leftBoundaryVertices_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real} :
-- imply
  E.axisNeg.rectLeftBoundaryVertices a b c d = E.rectRightBoundaryVertices (-b) (-a) (-d) (-c) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisNeg_leftBoundaryVertices E a b c d

/--
[PeriodicPlaneEmbedding.axisNeg_leftBoundaryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisNegation.lean)
-/
@[path]
private lemma axisNeg_leftBoundaryEvent_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {S : Set V} :
-- imply
  E.axisNeg.rectSideConnectionEvent a b c d S (E.axisNeg.rectLeftBoundaryVertices a b c d) = E.rectSideConnectionEvent (-b) (-a) (-d) (-c) S (E.rectRightBoundaryVertices (-b) (-a) (-d) (-c)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisNeg_leftBoundaryEvent E a b c d S

/--
[PeriodicPlaneEmbedding.exists_rightBoundaryPlacement_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisNegation.lean)
-/
@[path]
private lemma exists_rightBoundaryPlacement_tendsto_one_eq
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
  ∃ source : Nat → Finset V, ∃ radius : Nat → Nat, (∀ N, (source N : Set V) ⊆ E.rectVertices (-(r + radius N)) (-r) (-(radius N : Real)) (radius N)) ∧ Tendsto (fun N => mu.real (E.rectSideConnectionEvent (-(r + radius N)) (-r) (-(radius N : Real)) (radius N) (source N : Set V) (E.rectRightBoundaryVertices (-(r + radius N)) (-r) (-(radius N : Real)) (radius N)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_rightBoundaryPlacement_tendsto_one E mu hFKG hTI hunique r

/--
[PeriodicPlaneEmbedding.exists_translatedOrbitBox_rightBoundaryPlacement_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisNegation.lean)
-/
@[path]
private lemma exists_translatedOrbitBox_rightBoundaryPlacement_tendsto_one_eq
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
  ∃ base : Nat → Site 2, ∃ radius : Nat → Nat, (∀ N, (P.shift (base N) '' (P.orbitBox N : Set V)) ⊆ E.rectVertices (-(r + radius N)) (-r) (-(radius N : Real)) (radius N)) ∧ Tendsto (fun N => mu.real (E.rectSideConnectionEvent (-(r + radius N)) (-r) (-(radius N : Real)) (radius N) (P.shift (base N) '' (P.orbitBox N : Set V)) (E.rectRightBoundaryVertices (-(r + radius N)) (-r) (-(radius N : Real)) (radius N)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_translatedOrbitBox_rightBoundaryPlacement_tendsto_one E mu hFKG hTI hunique r

/--
[PeriodicPlaneEmbedding.exists_buffered_rightBoundaryPlacement_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisNegation.lean)
-/
@[path]
private lemma exists_buffered_rightBoundaryPlacement_tendsto_one_eq
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
  ∃ base : Nat → Site 2, ∃ radius : Nat → Nat, (∀ N, (P.shift (base N) '' (P.orbitBox (buffer N) : Set V)) ⊆ E.rectVertices (-(r + radius N)) (-r) (-(radius N : Real)) (radius N)) ∧ Tendsto (fun N => mu.real (E.rectSideConnectionEvent (-(r + radius N)) (-r) (-(radius N : Real)) (radius N) (P.shift (base N) '' (P.orbitBox N : Set V)) (E.rectRightBoundaryVertices (-(r + radius N)) (-r) (-(radius N : Real)) (radius N)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_buffered_rightBoundaryPlacement_tendsto_one E mu hFKG hTI hunique buffer hbuffer r


-- created on 2026-10-23
