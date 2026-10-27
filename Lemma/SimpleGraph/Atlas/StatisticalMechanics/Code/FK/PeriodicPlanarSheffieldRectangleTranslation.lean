import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectangleTranslation
open MeasureTheory Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.shift_mem_rectVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleTranslation.lean)
-/
@[path]
private lemma shift_mem_rectVertices_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {z : Site 2}
  {a b c d : Real}
  {x : V} :
-- imply
  P.shift z x ∈ E.rectVertices (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)) ↔ x ∈ E.rectVertices a b c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_mem_rectVertices E z a b c d x

/--
[PeriodicPlaneEmbedding.shift_image_rectVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleTranslation.lean)
-/
@[path]
private lemma shift_image_rectVertices_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {z : Site 2}
  {a b c d : Real} :
-- imply
  P.shift z '' E.rectVertices a b c d = E.rectVertices (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_image_rectVertices E z a b c d

/--
[PeriodicPlaneEmbedding.shift_mem_rectBottomBoundaryVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleTranslation.lean)
-/
@[path]
private lemma shift_mem_rectBottomBoundaryVertices_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {z : Site 2}
  {a b c d : Real}
  {x : V} :
-- imply
  P.shift z x ∈ E.rectBottomBoundaryVertices (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)) ↔ x ∈ E.rectBottomBoundaryVertices a b c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_mem_rectBottomBoundaryVertices E z a b c d x

/--
[PeriodicPlaneEmbedding.shift_mem_rectTopBoundaryVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleTranslation.lean)
-/
@[path]
private lemma shift_mem_rectTopBoundaryVertices_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {z : Site 2}
  {a b c d : Real}
  {x : V} :
-- imply
  P.shift z x ∈ E.rectTopBoundaryVertices (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)) ↔ x ∈ E.rectTopBoundaryVertices a b c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_mem_rectTopBoundaryVertices E z a b c d x

/--
[PeriodicPlaneEmbedding.shift_mem_rectLeftBoundaryVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleTranslation.lean)
-/
@[path]
private lemma shift_mem_rectLeftBoundaryVertices_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {z : Site 2}
  {a b c d : Real}
  {x : V} :
-- imply
  P.shift z x ∈ E.rectLeftBoundaryVertices (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)) ↔ x ∈ E.rectLeftBoundaryVertices a b c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_mem_rectLeftBoundaryVertices E z a b c d x

/--
[PeriodicPlaneEmbedding.shift_mem_rectRightBoundaryVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleTranslation.lean)
-/
@[path]
private lemma shift_mem_rectRightBoundaryVertices_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {z : Site 2}
  {a b c d : Real}
  {x : V} :
-- imply
  P.shift z x ∈ E.rectRightBoundaryVertices (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)) ↔ x ∈ E.rectRightBoundaryVertices a b c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_mem_rectRightBoundaryVertices E z a b c d x

/--
[PeriodicPlaneEmbedding.shift_image_rectBottomBoundaryVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleTranslation.lean)
-/
@[path]
private lemma shift_image_rectBottomBoundaryVertices_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {z : Site 2}
  {a b c d : Real} :
-- imply
  P.shift z '' E.rectBottomBoundaryVertices a b c d = E.rectBottomBoundaryVertices (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_image_rectBottomBoundaryVertices E z a b c d

/--
[PeriodicPlaneEmbedding.shift_image_rectTopBoundaryVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleTranslation.lean)
-/
@[path]
private lemma shift_image_rectTopBoundaryVertices_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {z : Site 2}
  {a b c d : Real} :
-- imply
  P.shift z '' E.rectTopBoundaryVertices a b c d = E.rectTopBoundaryVertices (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_image_rectTopBoundaryVertices E z a b c d

/--
[PeriodicPlaneEmbedding.shift_image_rectLeftBoundaryVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleTranslation.lean)
-/
@[path]
private lemma shift_image_rectLeftBoundaryVertices_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {z : Site 2}
  {a b c d : Real} :
-- imply
  P.shift z '' E.rectLeftBoundaryVertices a b c d = E.rectLeftBoundaryVertices (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_image_rectLeftBoundaryVertices E z a b c d

/--
[PeriodicPlaneEmbedding.shift_image_rectRightBoundaryVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleTranslation.lean)
-/
@[path]
private lemma shift_image_rectRightBoundaryVertices_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {z : Site 2}
  {a b c d : Real} :
-- imply
  P.shift z '' E.rectRightBoundaryVertices a b c d = E.rectRightBoundaryVertices (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_image_rectRightBoundaryVertices E z a b c d

/--
[PeriodicPlaneEmbedding.rectSideConnectionEvent_translate_measureReal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleTranslation.lean)
-/
@[path]
private lemma rectSideConnectionEvent_translate_measureReal_eq_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {z : Site 2}
  {a b c d : Real}
  {S side : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (E.rectSideConnectionEvent (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)) (P.shift z '' S) (P.shift z '' side)) = mu.real (E.rectSideConnectionEvent a b c d S side) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectSideConnectionEvent_translate_measureReal_eq E mu hTI z a b c d S side

/--
[PeriodicPlaneEmbedding.rectLeftConnection_translate_measureReal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleTranslation.lean)
-/
@[path]
private lemma rectLeftConnection_translate_measureReal_eq_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {z : Site 2}
  {a b c d : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (E.rectSideConnectionEvent (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)) (P.shift z '' S) (E.rectLeftBoundaryVertices (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)))) = mu.real (E.rectSideConnectionEvent a b c d S (E.rectLeftBoundaryVertices a b c d)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectLeftConnection_translate_measureReal_eq E mu hTI z a b c d S

/--
[PeriodicPlaneEmbedding.rectRightConnection_translate_measureReal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleTranslation.lean)
-/
@[path]
private lemma rectRightConnection_translate_measureReal_eq_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {z : Site 2}
  {a b c d : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (E.rectSideConnectionEvent (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)) (P.shift z '' S) (E.rectRightBoundaryVertices (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)))) = mu.real (E.rectSideConnectionEvent a b c d S (E.rectRightBoundaryVertices a b c d)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectRightConnection_translate_measureReal_eq E mu hTI z a b c d S

/--
[PeriodicPlaneEmbedding.rectBottomConnection_translate_measureReal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleTranslation.lean)
-/
@[path]
private lemma rectBottomConnection_translate_measureReal_eq_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {z : Site 2}
  {a b c d : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (E.rectSideConnectionEvent (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)) (P.shift z '' S) (E.rectBottomBoundaryVertices (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)))) = mu.real (E.rectSideConnectionEvent a b c d S (E.rectBottomBoundaryVertices a b c d)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectBottomConnection_translate_measureReal_eq E mu hTI z a b c d S

/--
[PeriodicPlaneEmbedding.rectTopConnection_translate_measureReal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectangleTranslation.lean)
-/
@[path]
private lemma rectTopConnection_translate_measureReal_eq_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {z : Site 2}
  {a b c d : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (E.rectSideConnectionEvent (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)) (P.shift z '' S) (E.rectTopBoundaryVertices (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real)))) = mu.real (E.rectSideConnectionEvent a b c d S (E.rectTopBoundaryVertices a b c d)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectTopConnection_translate_measureReal_eq E mu hTI z a b c d S


-- created on 2026-10-23
