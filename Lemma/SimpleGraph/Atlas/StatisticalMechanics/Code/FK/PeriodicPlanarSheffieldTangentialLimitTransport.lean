import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldTangentialLimitTransport
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.rectLeftConnection_tangential_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldTangentialLimitTransport.lean)
-/
@[path]
private lemma rectLeftConnection_tangential_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {z : Nat → Site 2}
  {a b c d b' c' d' : Nat → Real}
  {S : Nat → Set V}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hz : ∀ n, z n 0 = 0)
  (hb : ∀ n, b n + (z n 0 : Real) ≤ b' n)
  (hc : ∀ n, c' n ≤ c n + (z n 1 : Real))
  (hd : ∀ n, d n + (z n 1 : Real) ≤ d' n)
  (hlimit : Tendsto (fun n => mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (S n) (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => mu.real (E.rectSideConnectionEvent (a n) (b' n) (c' n) (d' n) (P.shift (z n) '' S n) (E.rectLeftBoundaryVertices (a n) (b' n) (c' n) (d' n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectLeftConnection_tangential_tendsto_one E mu hTI z hz a b c d b' c' d' S hb hc hd hlimit

/--
[PeriodicPlaneEmbedding.rectRightConnection_tangential_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldTangentialLimitTransport.lean)
-/
@[path]
private lemma rectRightConnection_tangential_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {z : Nat → Site 2}
  {a b c d a' c' d' : Nat → Real}
  {S : Nat → Set V}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hz : ∀ n, z n 0 = 0)
  (ha : ∀ n, a' n ≤ a n + (z n 0 : Real))
  (hc : ∀ n, c' n ≤ c n + (z n 1 : Real))
  (hd : ∀ n, d n + (z n 1 : Real) ≤ d' n)
  (hlimit : Tendsto (fun n => mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (S n) (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => mu.real (E.rectSideConnectionEvent (a' n) (b n) (c' n) (d' n) (P.shift (z n) '' S n) (E.rectRightBoundaryVertices (a' n) (b n) (c' n) (d' n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectRightConnection_tangential_tendsto_one E mu hTI z hz a b c d a' c' d' S ha hc hd hlimit

/--
[PeriodicPlaneEmbedding.rectBottomConnection_tangential_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldTangentialLimitTransport.lean)
-/
@[path]
private lemma rectBottomConnection_tangential_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {z : Nat → Site 2}
  {a b c d a' b' d' : Nat → Real}
  {S : Nat → Set V}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hz : ∀ n, z n 1 = 0)
  (ha : ∀ n, a' n ≤ a n + (z n 0 : Real))
  (hb : ∀ n, b n + (z n 0 : Real) ≤ b' n)
  (hd : ∀ n, d n + (z n 1 : Real) ≤ d' n)
  (hlimit : Tendsto (fun n => mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (S n) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => mu.real (E.rectSideConnectionEvent (a' n) (b' n) (c n) (d' n) (P.shift (z n) '' S n) (E.rectBottomBoundaryVertices (a' n) (b' n) (c n) (d' n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectBottomConnection_tangential_tendsto_one E mu hTI z hz a b c d a' b' d' S ha hb hd hlimit

/--
[PeriodicPlaneEmbedding.rectTopConnection_tangential_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldTangentialLimitTransport.lean)
-/
@[path]
private lemma rectTopConnection_tangential_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {z : Nat → Site 2}
  {a b c d a' b' c' : Nat → Real}
  {S : Nat → Set V}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hz : ∀ n, z n 1 = 0)
  (ha : ∀ n, a' n ≤ a n + (z n 0 : Real))
  (hb : ∀ n, b n + (z n 0 : Real) ≤ b' n)
  (hc : ∀ n, c' n ≤ c n + (z n 1 : Real))
  (hlimit : Tendsto (fun n => mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) (S n) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => mu.real (E.rectSideConnectionEvent (a' n) (b' n) (c' n) (d n) (P.shift (z n) '' S n) (E.rectTopBoundaryVertices (a' n) (b' n) (c' n) (d n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectTopConnection_tangential_tendsto_one E mu hTI z hz a b c d a' b' c' S ha hb hc hlimit


-- created on 2026-10-23
