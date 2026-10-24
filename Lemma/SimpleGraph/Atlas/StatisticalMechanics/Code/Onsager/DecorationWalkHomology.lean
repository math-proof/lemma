import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.DecorationWalkHomology
open StatMech StatMech.Onsager


/--
[ons_decCycleDartList_ofFn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkHomology.lean)
-/
@[path]
private lemma ons_decCycleDartList_ofFn_eq
  {L : ℕ}
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d} :
-- imply
  List.ofFn (ons_decCycleDartLoop q) = ons_decCycleDartList q := by
-- proof
  apply StatMech.Onsager.ons_decCycleDartList_ofFn q

/--
[ons_decCycleDartList_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkHomology.lean)
-/
@[path]
private lemma ons_decCycleDartList_eq_eq
  {L : ℕ}
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d} :
-- imply
  ons_decCycleDartList q = d :: (ons_decWalkExternalDarts q).tail.reverse := by
-- proof
  apply StatMech.Onsager.ons_decCycleDartList_eq q

/--
[ons_decCycleDartLoop_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkHomology.lean)
-/
@[path]
private lemma ons_decCycleDartLoop_zero_eq
  {L : ℕ}
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d} :
-- imply
  ons_decCycleDartLoop q 0 = d := by
-- proof
  apply StatMech.Onsager.ons_decCycleDartLoop_zero q

/--
[ons_decCycleDartLoop_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkHomology.lean)
-/
@[path]
private lemma ons_decCycleDartLoop_valid_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ∀ k : Fin (ons_decCycleDartList q).length, (ons_decCycleDartLoop q k).1 = ons_dirStep L (ons_decCycleDartLoop q (k + 1)).2 (ons_decCycleDartLoop q (k + 1)).1 := by
-- proof
  apply StatMech.Onsager.ons_decCycleDartLoop_valid q hq hsnd

/--
[ons_decCycleDartLoop_portEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkHomology.lean)
-/
@[path]
private lemma ons_decCycleDartLoop_portEdge_injective_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  Function.Injective (fun k : Fin (ons_decCycleDartList q).length => ons_portEdge L (ons_decCycleDartLoop q k)) := by
-- proof
  apply StatMech.Onsager.ons_decCycleDartLoop_portEdge_injective q hq hsnd

/--
[ons_decCycleDartLoop_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkHomology.lean)
-/
@[path]
private lemma ons_decCycleDartLoop_edgeSet_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ons_dartEdgeSet (ons_decCycleDartLoop q) = ons_walkOriginalEdges q := by
-- proof
  apply StatMech.Onsager.ons_decCycleDartLoop_edgeSet q hq hsnd

/--
[ons_dartEdgeSet_xSeam_card_of_portEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkHomology.lean)
-/
@[path]
private lemma ons_dartEdgeSet_xSeam_card_of_portEdge_injective_eq
  {L n : ℕ}
  [Fact (2 < L)]
  {d : Fin n → ons_Dart L}
-- given
  (hinj : Function.Injective (fun k => ons_portEdge L (d k))) :
-- imply
  ((ons_dartEdgeSet d).filter (ons_xSeamEdge L)).card = (Finset.univ.filter (fun k => ons_xWrap (d k))).card := by
-- proof
  apply StatMech.Onsager.ons_dartEdgeSet_xSeam_card_of_portEdge_injective d hinj

/--
[ons_dartEdgeSet_ySeam_card_of_portEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkHomology.lean)
-/
@[path]
private lemma ons_dartEdgeSet_ySeam_card_of_portEdge_injective_eq
  {L n : ℕ}
  [Fact (2 < L)]
  {d : Fin n → ons_Dart L}
-- given
  (hinj : Function.Injective (fun k => ons_portEdge L (d k))) :
-- imply
  ((ons_dartEdgeSet d).filter (ons_ySeamEdge L)).card = (Finset.univ.filter (fun k => ons_yWrap (d k))).card := by
-- proof
  apply StatMech.Onsager.ons_dartEdgeSet_ySeam_card_of_portEdge_injective d hinj

/--
[ons_evenHomology_dartEdgeSet_eq_windingParity_of_portEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkHomology.lean)
-/
@[path]
private lemma ons_evenHomology_dartEdgeSet_eq_windingParity_of_portEdge_injective_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {d : Fin n → ons_Dart L}
  {mx my : ℤ}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hinj : Function.Injective (fun k => ons_portEdge L (d k)))
  (hmx : (∑ k, ons_dirExponentX (d k).2) = (L : ℤ) * mx)
  (hmy : (∑ k, ons_dirExponentY (d k).2) = (L : ℤ) * my) :
-- imply
  ons_evenHomology L (ons_dartEdgeSet d) = ons_windingParity mx my := by
-- proof
  apply StatMech.Onsager.ons_evenHomology_dartEdgeSet_eq_windingParity_of_portEdge_injective d hvalid hinj mx my hmx hmy

/--
[ons_decCycle_spinPhase_product_eq_homology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkHomology.lean)
-/
@[path]
private lemma ons_decCycle_spinPhase_product_eq_homology_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {a b : Fin 2}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  (∏ k, ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) (ons_decCycleDartLoop q k).2) = ons_spinLinearCharacter a b (ons_evenHomology L (ons_walkOriginalEdges q)) := by
-- proof
  apply StatMech.Onsager.ons_decCycle_spinPhase_product_eq_homology q hq hsnd a b


-- created on 2026-10-23
