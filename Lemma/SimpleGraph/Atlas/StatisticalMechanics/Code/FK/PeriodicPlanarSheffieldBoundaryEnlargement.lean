import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryEnlargement
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.exists_buffered_leftBoundaryPlacement_enlargeable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryEnlargement.lean)
-/
@[path]
private lemma exists_buffered_leftBoundaryPlacement_enlargeable_eq
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
  ∃ base : Nat → Site 2, ∃ radius : Nat → Nat, ∀ (b c d : Nat → Real), (∀ N, r + radius N ≤ b N) → (∀ N, c N ≤ -(radius N : Real)) → (∀ N, (radius N : Real) ≤ d N) → (∀ N, (P.shift (base N) '' (P.orbitBox (buffer N) : Set V)) ⊆ E.rectVertices r (b N) (c N) (d N)) ∧ Tendsto (fun N => mu.real (E.rectSideConnectionEvent r (b N) (c N) (d N) (P.shift (base N) '' (P.orbitBox N : Set V)) (E.rectLeftBoundaryVertices r (b N) (c N) (d N)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_buffered_leftBoundaryPlacement_enlargeable E mu hFKG hTI hunique buffer hbuffer r

/--
[PeriodicPlaneEmbedding.exists_buffered_rightBoundaryPlacement_enlargeable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryEnlargement.lean)
-/
@[path]
private lemma exists_buffered_rightBoundaryPlacement_enlargeable_eq
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
  ∃ base : Nat → Site 2, ∃ radius : Nat → Nat, ∀ (a c d : Nat → Real), (∀ N, a N ≤ -(r + radius N)) → (∀ N, c N ≤ -(radius N : Real)) → (∀ N, (radius N : Real) ≤ d N) → (∀ N, (P.shift (base N) '' (P.orbitBox (buffer N) : Set V)) ⊆ E.rectVertices (a N) (-r) (c N) (d N)) ∧ Tendsto (fun N => mu.real (E.rectSideConnectionEvent (a N) (-r) (c N) (d N) (P.shift (base N) '' (P.orbitBox N : Set V)) (E.rectRightBoundaryVertices (a N) (-r) (c N) (d N)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_buffered_rightBoundaryPlacement_enlargeable E mu hFKG hTI hunique buffer hbuffer r

/--
[PeriodicPlaneEmbedding.exists_buffered_bottomBoundaryPlacement_enlargeable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryEnlargement.lean)
-/
@[path]
private lemma exists_buffered_bottomBoundaryPlacement_enlargeable_eq
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
  ∃ base : Nat → Site 2, ∃ radius : Nat → Nat, ∀ (a b d : Nat → Real), (∀ N, a N ≤ -(radius N : Real)) → (∀ N, (radius N : Real) ≤ b N) → (∀ N, r + radius N ≤ d N) → (∀ N, (P.shift (base N) '' (P.orbitBox (buffer N) : Set V)) ⊆ E.rectVertices (a N) (b N) r (d N)) ∧ Tendsto (fun N => mu.real (E.rectSideConnectionEvent (a N) (b N) r (d N) (P.shift (base N) '' (P.orbitBox N : Set V)) (E.rectBottomBoundaryVertices (a N) (b N) r (d N)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_buffered_bottomBoundaryPlacement_enlargeable E mu hFKG hTI hunique buffer hbuffer r

/--
[PeriodicPlaneEmbedding.exists_buffered_topBoundaryPlacement_enlargeable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryEnlargement.lean)
-/
@[path]
private lemma exists_buffered_topBoundaryPlacement_enlargeable_eq
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
  ∃ base : Nat → Site 2, ∃ radius : Nat → Nat, ∀ (a b c : Nat → Real), (∀ N, a N ≤ -(radius N : Real)) → (∀ N, (radius N : Real) ≤ b N) → (∀ N, c N ≤ -(r + radius N)) → (∀ N, (P.shift (base N) '' (P.orbitBox (buffer N) : Set V)) ⊆ E.rectVertices (a N) (b N) (c N) (-r)) ∧ Tendsto (fun N => mu.real (E.rectSideConnectionEvent (a N) (b N) (c N) (-r) (P.shift (base N) '' (P.orbitBox N : Set V)) (E.rectTopBoundaryVertices (a N) (b N) (c N) (-r)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_buffered_topBoundaryPlacement_enlargeable E mu hFKG hTI hunique buffer hbuffer r


-- created on 2026-10-23
