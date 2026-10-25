import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationWalkExtract.Part2
open StatMech StatMech.Onsager


/--
[ons_decWalkExternalDarts_cons_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkExtract.lean)
-/
@[path]
private lemma ons_decWalkExternalDarts_cons_external_eq
  {L : ℕ}
  {u v w : ons_Dart L}
  {p : (ons_decGraph L).Walk v w}
-- given
  (h : (ons_decGraph L).Adj u v)
  (hrev : v = ons_dartRev L u) :
-- imply
  ons_decWalkExternalDarts (SimpleGraph.Walk.cons h p) = u :: ons_decWalkExternalDarts p := by
-- proof
  apply StatMech.Onsager.ons_decWalkExternalDarts_cons_external h p hrev

/--
[ons_decWalkExternalDarts_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkExtract.lean)
-/
@[path]
private lemma ons_decWalkExternalDarts_head_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  (ons_decWalkExternalDarts q).head? = some d := by
-- proof
  apply StatMech.Onsager.ons_decWalkExternalDarts_head q hq hsnd

/--
[ons_decWalkExternalDarts_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkExtract.lean)
-/
@[path]
private lemma ons_decWalkExternalDarts_nodup_eq
  {L : ℕ}
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle) :
-- imply
  (ons_decWalkExternalDarts q).Nodup := by
-- proof
  apply StatMech.Onsager.ons_decWalkExternalDarts_nodup q hq

/--
[ons_externalEdge_mem_edges_of_mem_decWalkExternalDarts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkExtract.lean)
-/
@[path]
private lemma ons_externalEdge_mem_edges_of_mem_decWalkExternalDarts_eq
  {L : ℕ}
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v}
  {d : ons_Dart L}
-- given
  (hd : d ∈ ons_decWalkExternalDarts p) :
-- imply
  s(d, ons_dartRev L d) ∈ p.edges := by
-- proof
  apply StatMech.Onsager.ons_externalEdge_mem_edges_of_mem_decWalkExternalDarts p hd

/--
[ons_decWalkExternalDarts_image_portEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkExtract.lean)
-/
@[path]
private lemma ons_decWalkExternalDarts_image_portEdge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v} :
-- imply
  (ons_decWalkExternalDarts p).toFinset.image (ons_portEdge L) = ons_walkOriginalEdges p := by
-- proof
  apply StatMech.Onsager.ons_decWalkExternalDarts_image_portEdge p

/--
[ons_decWalkExternalEdges_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkExtract.lean)
-/
@[path]
private lemma ons_decWalkExternalEdges_nodup_eq
  {L : ℕ}
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle) :
-- imply
  ((ons_decWalkExternalDarts q).map (fun e => s(e, ons_dartRev L e))).Nodup := by
-- proof
  apply StatMech.Onsager.ons_decWalkExternalEdges_nodup q hq

/--
[ons_decWalkExternalDarts_portEdge_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkExtract.lean)
-/
@[path]
private lemma ons_decWalkExternalDarts_portEdge_nodup_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle) :
-- imply
  ((ons_decWalkExternalDarts q).map (ons_portEdge L)).Nodup := by
-- proof
  apply StatMech.Onsager.ons_decWalkExternalDarts_portEdge_nodup q hq

/--
[ons_walkOriginalEdges_prod_eq_externalDarts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkExtract.lean)
-/
@[path]
private lemma ons_walkOriginalEdges_prod_eq_externalDarts_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
-- given
  (hq : q.IsCycle) :
-- imply
  ∏ edge ∈ ons_walkOriginalEdges q, weight edge = ((ons_decWalkExternalDarts q).map (fun e => weight (ons_portEdge L e))).prod := by
-- proof
  apply StatMech.Onsager.ons_walkOriginalEdges_prod_eq_externalDarts q hq weight

/--
[ons_decCycleFirstReturn_isFirstReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkExtract.lean)
-/
@[path]
private lemma ons_decCycleFirstReturn_isFirstReturn_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ons_isFirstReturnSegment d (ons_decCycleFirstReturn q) := by
-- proof
  apply StatMech.Onsager.ons_decCycleFirstReturn_isFirstReturn q hq hsnd

/--
[ons_decCycleFirstReturn_avoids_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkExtract.lean)
-/
@[path]
private lemma ons_decCycleFirstReturn_avoids_reverse_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ∀ e ∈ ons_decCycleFirstReturn q, e ≠ ons_dartRev L d := by
-- proof
  apply StatMech.Onsager.ons_decCycleFirstReturn_avoids_reverse q hq hsnd

/--
[ons_decCycleFirstReturn_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkExtract.lean)
-/
@[path]
private lemma ons_decCycleFirstReturn_valid_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ons_isFirstReturnSegment d (ons_decCycleFirstReturn q) ∧ ∀ e ∈ ons_decCycleFirstReturn q, e ≠ ons_dartRev L d := by
-- proof
  apply StatMech.Onsager.ons_decCycleFirstReturn_valid q hq hsnd


-- created on 2026-10-23
