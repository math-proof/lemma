import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldOrientedBoundary
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.axisSwap_orbitBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOrientedBoundary.lean)
-/
@[path]
private lemma axisSwap_orbitBox_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {n : Nat} :
-- imply
  P.axisSwap.orbitBox n = P.orbitBox n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.axisSwap_orbitBox P n

/--
[PeriodicPlaneEmbedding.axisSwap_rectVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOrientedBoundary.lean)
-/
@[path]
private lemma axisSwap_rectVertices_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real} :
-- imply
  E.axisSwap.rectVertices a b c d = E.rectVertices c d a b := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisSwap_rectVertices E a b c d

/--
[PeriodicPlaneEmbedding.axisSwap_leftBoundaryVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOrientedBoundary.lean)
-/
@[path]
private lemma axisSwap_leftBoundaryVertices_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real} :
-- imply
  E.axisSwap.rectLeftBoundaryVertices a b c d = E.rectBottomBoundaryVertices c d a b := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisSwap_leftBoundaryVertices E a b c d

/--
[PeriodicPlaneEmbedding.axisSwap_rightBoundaryVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOrientedBoundary.lean)
-/
@[path]
private lemma axisSwap_rightBoundaryVertices_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real} :
-- imply
  E.axisSwap.rectRightBoundaryVertices a b c d = E.rectTopBoundaryVertices c d a b := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisSwap_rightBoundaryVertices E a b c d

/--
[PeriodicPlaneEmbedding.axisSwap_leftBoundaryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOrientedBoundary.lean)
-/
@[path]
private lemma axisSwap_leftBoundaryEvent_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {S : Set V} :
-- imply
  E.axisSwap.rectSideConnectionEvent a b c d S (E.axisSwap.rectLeftBoundaryVertices a b c d) = E.rectSideConnectionEvent c d a b S (E.rectBottomBoundaryVertices c d a b) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisSwap_leftBoundaryEvent E a b c d S

/--
[PeriodicPlaneEmbedding.axisSwap_rightBoundaryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOrientedBoundary.lean)
-/
@[path]
private lemma axisSwap_rightBoundaryEvent_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {S : Set V} :
-- imply
  E.axisSwap.rectSideConnectionEvent a b c d S (E.axisSwap.rectRightBoundaryVertices a b c d) = E.rectSideConnectionEvent c d a b S (E.rectTopBoundaryVertices c d a b) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisSwap_rightBoundaryEvent E a b c d S

/--
[PeriodicPlaneEmbedding.exists_bottomBoundaryPlacement_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOrientedBoundary.lean)
-/
@[path]
private lemma exists_bottomBoundaryPlacement_tendsto_one_eq
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
  ∃ source : Nat → Finset V, ∃ radius : Nat → Nat, (∀ N, (source N : Set V) ⊆ E.rectVertices (-(radius N : Real)) (radius N) r (r + radius N)) ∧ Tendsto (fun N => mu.real (E.rectSideConnectionEvent (-(radius N : Real)) (radius N) r (r + radius N) (source N : Set V) (E.rectBottomBoundaryVertices (-(radius N : Real)) (radius N) r (r + radius N)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_bottomBoundaryPlacement_tendsto_one E mu hFKG hTI hunique r

/--
[PeriodicPlaneEmbedding.exists_topBoundaryPlacement_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOrientedBoundary.lean)
-/
@[path]
private lemma exists_topBoundaryPlacement_tendsto_one_eq
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
  ∃ source : Nat → Finset V, ∃ radius : Nat → Nat, (∀ N, (source N : Set V) ⊆ E.rectVertices (-(radius N : Real)) (radius N) (-(r + radius N)) (-r)) ∧ Tendsto (fun N => mu.real (E.rectSideConnectionEvent (-(radius N : Real)) (radius N) (-(r + radius N)) (-r) (source N : Set V) (E.rectTopBoundaryVertices (-(radius N : Real)) (radius N) (-(r + radius N)) (-r)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_topBoundaryPlacement_tendsto_one E mu hFKG hTI hunique r

/--
[PeriodicPlaneEmbedding.exists_translatedOrbitBox_bottomBoundaryPlacement_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOrientedBoundary.lean)
-/
@[path]
private lemma exists_translatedOrbitBox_bottomBoundaryPlacement_tendsto_one_eq
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
  ∃ base : Nat → Site 2, ∃ radius : Nat → Nat, (∀ N, (P.shift (base N) '' (P.orbitBox N : Set V)) ⊆ E.rectVertices (-(radius N : Real)) (radius N) r (r + radius N)) ∧ Tendsto (fun N => mu.real (E.rectSideConnectionEvent (-(radius N : Real)) (radius N) r (r + radius N) (P.shift (base N) '' (P.orbitBox N : Set V)) (E.rectBottomBoundaryVertices (-(radius N : Real)) (radius N) r (r + radius N)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_translatedOrbitBox_bottomBoundaryPlacement_tendsto_one E mu hFKG hTI hunique r

/--
[PeriodicPlaneEmbedding.exists_translatedOrbitBox_topBoundaryPlacement_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOrientedBoundary.lean)
-/
@[path]
private lemma exists_translatedOrbitBox_topBoundaryPlacement_tendsto_one_eq
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
  ∃ base : Nat → Site 2, ∃ radius : Nat → Nat, (∀ N, (P.shift (base N) '' (P.orbitBox N : Set V)) ⊆ E.rectVertices (-(radius N : Real)) (radius N) (-(r + radius N)) (-r)) ∧ Tendsto (fun N => mu.real (E.rectSideConnectionEvent (-(radius N : Real)) (radius N) (-(r + radius N)) (-r) (P.shift (base N) '' (P.orbitBox N : Set V)) (E.rectTopBoundaryVertices (-(radius N : Real)) (radius N) (-(r + radius N)) (-r)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_translatedOrbitBox_topBoundaryPlacement_tendsto_one E mu hFKG hTI hunique r

/--
[PeriodicPlaneEmbedding.exists_buffered_bottomBoundaryPlacement_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOrientedBoundary.lean)
-/
@[path]
private lemma exists_buffered_bottomBoundaryPlacement_tendsto_one_eq
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
  ∃ base : Nat → Site 2, ∃ radius : Nat → Nat, (∀ N, (P.shift (base N) '' (P.orbitBox (buffer N) : Set V)) ⊆ E.rectVertices (-(radius N : Real)) (radius N) r (r + radius N)) ∧ Tendsto (fun N => mu.real (E.rectSideConnectionEvent (-(radius N : Real)) (radius N) r (r + radius N) (P.shift (base N) '' (P.orbitBox N : Set V)) (E.rectBottomBoundaryVertices (-(radius N : Real)) (radius N) r (r + radius N)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_buffered_bottomBoundaryPlacement_tendsto_one E mu hFKG hTI hunique buffer hbuffer r

/--
[PeriodicPlaneEmbedding.exists_buffered_topBoundaryPlacement_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOrientedBoundary.lean)
-/
@[path]
private lemma exists_buffered_topBoundaryPlacement_tendsto_one_eq
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
  ∃ base : Nat → Site 2, ∃ radius : Nat → Nat, (∀ N, (P.shift (base N) '' (P.orbitBox (buffer N) : Set V)) ⊆ E.rectVertices (-(radius N : Real)) (radius N) (-(r + radius N)) (-r)) ∧ Tendsto (fun N => mu.real (E.rectSideConnectionEvent (-(radius N : Real)) (radius N) (-(r + radius N)) (-r) (P.shift (base N) '' (P.orbitBox N : Set V)) (E.rectTopBoundaryVertices (-(radius N : Real)) (radius N) (-(r + radius N)) (-r)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_buffered_topBoundaryPlacement_tendsto_one E mu hFKG hTI hunique buffer hbuffer r


-- created on 2026-10-23
