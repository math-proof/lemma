import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordPhaseGlue.Part2
open StatMech StatMech.FrontierA


/--
[KWFiniteSimplePolygon.prefixOfCleanChord_edgeList_eq_take](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordPhaseGlue.lean)
-/
@[path]
private lemma prefixOfCleanChord_edgeList_eq_take_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {j : Fin n}
-- given
  (hj : 2 ≤ j.val)
  (hclean : polygon.ChordIsClean 0 j) :
-- imply
  (polygon.prefixOfCleanChord j hj hclean).edgeList = (polygon.edgeList.take j.val).concat (polygon.vertex 0 - polygon.vertex j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.prefixOfCleanChord_edgeList_eq_take polygon j hj hclean

/--
[fin_zero_sub_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordPhaseGlue.lean)
-/
@[path]
private lemma fin_zero_sub_val_eq
  {n : ℕ}
  [NeZero n]
  {j : Fin n}
-- given
  (hj : j ≠ 0) :
-- imply
  ((0 : Fin n) - j).val = n - j.val := by
-- proof
  apply StatMech.FrontierA.fin_zero_sub_val j hj

/--
[KWFiniteSimplePolygon.complementOfCleanChord_edgeList_eq_drop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordPhaseGlue.lean)
-/
@[path]
private lemma complementOfCleanChord_edgeList_eq_drop_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {j : Fin n}
-- given
  (hj0 : j ≠ 0)
  (hd : 2 ≤ (-j).val)
  (hcleanRotated : (polygon.rotate j).ChordIsClean 0 (-j)) :
-- imply
  ((polygon.rotate j).prefixOfCleanChord (-j) hd hcleanRotated).edgeList = (polygon.edgeList.drop j.val).concat (polygon.vertex j - polygon.vertex 0) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.complementOfCleanChord_edgeList_eq_drop polygon j hj0 hd hcleanRotated

/--
[kwVectorPhasePath_append_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordPhaseGlue.lean)
-/
@[path]
private lemma kwVectorPhasePath_append_cons_eq
  {x : ℂ}
  {left : List ℂ}
  {y : ℂ}
  {right : List ℂ} :
-- imply
  kwVectorPhasePath ((x :: left) ++ y :: right) = kwVectorPhasePath (x :: left) * kwVectorTurnPhase ((x :: left).getLastD x) y * kwVectorPhasePath (y :: right) := by
-- proof
  apply StatMech.FrontierA.kwVectorPhasePath_append_cons x left y right

/--
[kwVectorPhaseCycle_append_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordPhaseGlue.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_append_cons_eq
  {x : ℂ}
  {left : List ℂ}
  {y : ℂ}
  {right : List ℂ} :
-- imply
  kwVectorPhaseCycle ((x :: left) ++ y :: right) = kwVectorPhasePath (x :: left) * kwVectorTurnPhase ((x :: left).getLastD x) y * kwVectorPhasePath (y :: right) * kwVectorTurnPhase ((y :: right).getLastD y) x := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_append_cons x left y right

/--
[kwVectorPhaseCycle_concat_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordPhaseGlue.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_concat_singleton_eq
  {x : ℂ}
  {tail : List ℂ}
  {chord : ℂ} :
-- imply
  kwVectorPhaseCycle ((x :: tail).concat chord) = kwVectorPhasePath (x :: tail) * kwVectorTurnPhase ((x :: tail).getLastD x) chord * kwVectorTurnPhase chord x := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_concat_singleton x tail chord

/--
[kwVectorPhaseCycle_chord_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordPhaseGlue.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_chord_glue_eq
  {pFirst : ℂ}
  {pTail : List ℂ}
  {qFirst : ℂ}
  {qTail : List ℂ}
  {chord : ℂ}
-- given
  (hboundary : kwVectorTurnPhase ((pFirst :: pTail).getLastD pFirst) qFirst * kwVectorTurnPhase ((qFirst :: qTail).getLastD qFirst) pFirst = -(kwVectorTurnPhase ((pFirst :: pTail).getLastD pFirst) (-chord) * kwVectorTurnPhase (-chord) pFirst * (kwVectorTurnPhase ((qFirst :: qTail).getLastD qFirst) chord * kwVectorTurnPhase chord qFirst))) :
-- imply
  kwVectorPhaseCycle ((pFirst :: pTail) ++ qFirst :: qTail) = -(kwVectorPhaseCycle ((pFirst :: pTail).concat (-chord)) * kwVectorPhaseCycle ((qFirst :: qTail).concat chord)) := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_chord_glue pFirst pTail qFirst qTail chord hboundary

/--
[kwVectorPhaseCycle_chord_glue_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordPhaseGlue.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_chord_glue_eq_neg_one_eq
  {pFirst : ℂ}
  {pTail : List ℂ}
  {qFirst : ℂ}
  {qTail : List ℂ}
  {chord : ℂ}
-- given
  (hboundary : kwVectorTurnPhase ((pFirst :: pTail).getLastD pFirst) qFirst * kwVectorTurnPhase ((qFirst :: qTail).getLastD qFirst) pFirst = -(kwVectorTurnPhase ((pFirst :: pTail).getLastD pFirst) (-chord) * kwVectorTurnPhase (-chord) pFirst * (kwVectorTurnPhase ((qFirst :: qTail).getLastD qFirst) chord * kwVectorTurnPhase chord qFirst)))
  (hp : kwVectorPhaseCycle ((pFirst :: pTail).concat (-chord)) = -1)
  (hq : kwVectorPhaseCycle ((qFirst :: qTail).concat chord) = -1) :
-- imply
  kwVectorPhaseCycle ((pFirst :: pTail) ++ qFirst :: qTail) = -1 := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_chord_glue_eq_neg_one pFirst pTail qFirst qTail chord hboundary hp hq

/--
[kwVectorPhaseCycle_chord_glue_lists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordPhaseGlue.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_chord_glue_lists_eq
  {p q : List ℂ}
  {chord : ℂ}
-- given
  (hpne : p ≠ [])
  (hqne : q ≠ [])
  (hboundary : kwVectorTurnPhase (p.getLast hpne) (q.head hqne) * kwVectorTurnPhase (q.getLast hqne) (p.head hpne) = -(kwVectorTurnPhase (p.getLast hpne) (-chord) * kwVectorTurnPhase (-chord) (p.head hpne) * (kwVectorTurnPhase (q.getLast hqne) chord * kwVectorTurnPhase chord (q.head hqne)))) :
-- imply
  kwVectorPhaseCycle (p ++ q) = -(kwVectorPhaseCycle (p.concat (-chord)) * kwVectorPhaseCycle (q.concat chord)) := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_chord_glue_lists p q hpne hqne chord hboundary

/--
[kwVectorPhaseCycle_chord_glue_lists_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordPhaseGlue.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_chord_glue_lists_eq_neg_one_eq
  {p q : List ℂ}
  {chord : ℂ}
-- given
  (hpne : p ≠ [])
  (hqne : q ≠ [])
  (hboundary : kwVectorTurnPhase (p.getLast hpne) (q.head hqne) * kwVectorTurnPhase (q.getLast hqne) (p.head hpne) = -(kwVectorTurnPhase (p.getLast hpne) (-chord) * kwVectorTurnPhase (-chord) (p.head hpne) * (kwVectorTurnPhase (q.getLast hqne) chord * kwVectorTurnPhase chord (q.head hqne))))
  (hp : kwVectorPhaseCycle (p.concat (-chord)) = -1)
  (hq : kwVectorPhaseCycle (q.concat chord) = -1) :
-- imply
  kwVectorPhaseCycle (p ++ q) = -1 := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_chord_glue_lists_eq_neg_one p q hpne hqne chord hboundary hp hq

/--
[KWFiniteSimplePolygon.phaseCycle_eq_neg_one_of_cleanChord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordPhaseGlue.lean)
-/
@[path]
private lemma phaseCycle_eq_neg_one_of_cleanChord_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {j : Fin n}
-- given
  (hj : 2 ≤ j.val)
  (hclean : polygon.ChordIsClean 0 j)
  (hd : 2 ≤ (-j).val)
  (hcleanRotated : (polygon.rotate j).ChordIsClean 0 (-j))
  (hcompatible : polygon.CleanChordBoundaryPhaseCompatible j (by omega))
  (hfirst : kwVectorPhaseCycle (polygon.prefixOfCleanChord j hj hclean).edgeList = -1)
  (hsecond : kwVectorPhaseCycle ((polygon.rotate j).prefixOfCleanChord (-j) hd hcleanRotated).edgeList = -1) :
-- imply
  kwVectorPhaseCycle polygon.edgeList = -1 := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.phaseCycle_eq_neg_one_of_cleanChord polygon j hj hclean hd hcleanRotated hcompatible hfirst hsecond

/--
[kwVectorPhaseCycle_contract_front_remaining](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordPhaseGlue.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_contract_front_remaining_eq
  {incoming outgoing : ℂ}
  {remaining : List ℂ}
-- given
  (hne : remaining ≠ [])
  (htail : remaining.tail ≠ [])
  (hlocal : kwVectorTurnPhase (remaining.tail.getLast htail) incoming * kwVectorTurnPhase incoming outgoing * kwVectorTurnPhase outgoing (remaining.head hne) = kwVectorTurnPhase (remaining.tail.getLast htail) (incoming + outgoing) * kwVectorTurnPhase (incoming + outgoing) (remaining.head hne)) :
-- imply
  kwVectorPhaseCycle (incoming :: outgoing :: remaining) = kwVectorPhaseCycle ((incoming + outgoing) :: remaining) := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_contract_front_remaining incoming outgoing remaining hne htail hlocal

/--
[KWFiniteSimplePolygon.phaseCycle_removeVertexOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordPhaseGlue.lean)
-/
@[path]
private lemma phaseCycle_removeVertexOne_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hsimple : polygon.VertexOneRemovalIsSimple)
  (hphase : polygon.VertexOnePhaseEar hm) :
-- imply
  kwVectorPhaseCycle polygon.edgeList = kwVectorPhaseCycle (polygon.removeVertexOne hm hsimple).edgeList := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.phaseCycle_removeVertexOne hm polygon hsimple hphase


-- created on 2026-10-23
