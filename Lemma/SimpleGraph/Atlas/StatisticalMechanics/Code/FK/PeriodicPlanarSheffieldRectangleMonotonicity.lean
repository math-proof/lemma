import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectangleMonotonicity
open Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.rectVertices_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleMonotonicity.lean)
-/
@[path]
private lemma rectVertices_mono_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d a' b' c' d' : Real}
-- given
  (ha : a' ≤ a)
  (hb : b ≤ b')
  (hc : c' ≤ c)
  (hd : d ≤ d') :
-- imply
  E.rectVertices a b c d ⊆ E.rectVertices a' b' c' d' := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectVertices_mono E ha hb hc hd

/--
[PeriodicPlaneEmbedding.rectLeftConnectionEvent_mono_otherBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleMonotonicity.lean)
-/
@[path]
private lemma rectLeftConnectionEvent_mono_otherBounds_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {S : Set V}
  {a b c d b' c' d' : Real}
-- given
  (hb : b ≤ b')
  (hc : c' ≤ c)
  (hd : d ≤ d') :
-- imply
  E.rectSideConnectionEvent a b c d S (E.rectLeftBoundaryVertices a b c d) ⊆ E.rectSideConnectionEvent a b' c' d' S (E.rectLeftBoundaryVertices a b' c' d') := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectLeftConnectionEvent_mono_otherBounds E S hb hc hd

/--
[PeriodicPlaneEmbedding.rectRightConnectionEvent_mono_otherBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleMonotonicity.lean)
-/
@[path]
private lemma rectRightConnectionEvent_mono_otherBounds_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {S : Set V}
  {a b c d a' c' d' : Real}
-- given
  (ha : a' ≤ a)
  (hc : c' ≤ c)
  (hd : d ≤ d') :
-- imply
  E.rectSideConnectionEvent a b c d S (E.rectRightBoundaryVertices a b c d) ⊆ E.rectSideConnectionEvent a' b c' d' S (E.rectRightBoundaryVertices a' b c' d') := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectRightConnectionEvent_mono_otherBounds E S ha hc hd

/--
[PeriodicPlaneEmbedding.rectBottomConnectionEvent_mono_otherBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleMonotonicity.lean)
-/
@[path]
private lemma rectBottomConnectionEvent_mono_otherBounds_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {S : Set V}
  {a b c d a' b' d' : Real}
-- given
  (ha : a' ≤ a)
  (hb : b ≤ b')
  (hd : d ≤ d') :
-- imply
  E.rectSideConnectionEvent a b c d S (E.rectBottomBoundaryVertices a b c d) ⊆ E.rectSideConnectionEvent a' b' c d' S (E.rectBottomBoundaryVertices a' b' c d') := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectBottomConnectionEvent_mono_otherBounds E S ha hb hd

/--
[PeriodicPlaneEmbedding.rectTopConnectionEvent_mono_otherBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleMonotonicity.lean)
-/
@[path]
private lemma rectTopConnectionEvent_mono_otherBounds_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {S : Set V}
  {a b c d a' b' c' : Real}
-- given
  (ha : a' ≤ a)
  (hb : b ≤ b')
  (hc : c' ≤ c) :
-- imply
  E.rectSideConnectionEvent a b c d S (E.rectTopBoundaryVertices a b c d) ⊆ E.rectSideConnectionEvent a' b' c' d S (E.rectTopBoundaryVertices a' b' c' d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectTopConnectionEvent_mono_otherBounds E S ha hb hc


-- created on 2026-10-23
