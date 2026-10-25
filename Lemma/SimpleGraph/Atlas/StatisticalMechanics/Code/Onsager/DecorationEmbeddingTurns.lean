import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbeddingTurns.Part5
open StatMech StatMech.Onsager


/--
[ons_decEdgeMicroDarts_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decEdgeMicroDarts_length_eq
  {L : ℕ}
  {d e : ons_Dart L} :
-- imply
  (ons_decEdgeMicroDarts L d e).length = 4 := by
-- proof
  apply StatMech.Onsager.ons_decEdgeMicroDarts_length L d e

/--
[ons_decEdgeMicroDarts_sites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decEdgeMicroDarts_sites_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
-- given
  (hde : (ons_decGraph L).Adj d e) :
-- imply
  (ons_decEdgeMicroDarts L d e).map (fun a => a.1) = (ons_decEdgeRoute L d e hde).support.dropLast := by
-- proof
  apply StatMech.Onsager.ons_decEdgeMicroDarts_sites L d e hde

/--
[ons_decEdgeMicroDarts_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decEdgeMicroDarts_edges_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
-- given
  (hde : (ons_decGraph L).Adj d e) :
-- imply
  (ons_decEdgeMicroDarts L d e).map (ons_portEdge (8 * L)) = (ons_decEdgeRoute L d e hde).edges := by
-- proof
  apply StatMech.Onsager.ons_decEdgeMicroDarts_edges L d e hde

/--
[ons_decEdgeMicroDarts_sum_exponentX_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decEdgeMicroDarts_sum_exponentX_external_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
-- given
  (hrev : e = ons_dartRev L d) :
-- imply
  ((ons_decEdgeMicroDarts L d e).map (fun a => ons_dirExponentX a.2)).sum = 4 * ons_dirExponentX d.2 := by
-- proof
  apply StatMech.Onsager.ons_decEdgeMicroDarts_sum_exponentX_external L d e hrev

/--
[ons_decEdgeMicroDarts_sum_exponentY_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decEdgeMicroDarts_sum_exponentY_external_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
-- given
  (hrev : e = ons_dartRev L d) :
-- imply
  ((ons_decEdgeMicroDarts L d e).map (fun a => ons_dirExponentY a.2)).sum = 4 * ons_dirExponentY d.2 := by
-- proof
  apply StatMech.Onsager.ons_decEdgeMicroDarts_sum_exponentY_external L d e hrev

/--
[ons_decEdgeMicroDarts_sum_exponentX_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decEdgeMicroDarts_sum_exponentX_internal_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
-- given
  (hint : ons_decInternalAdj d e) :
-- imply
  ((ons_decEdgeMicroDarts L d e).map (fun a => ons_dirExponentX a.2)).sum = 2 * (ons_dirExponentX e.2 - ons_dirExponentX d.2) := by
-- proof
  apply StatMech.Onsager.ons_decEdgeMicroDarts_sum_exponentX_internal L d e hint

/--
[ons_decEdgeMicroDarts_sum_exponentY_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decEdgeMicroDarts_sum_exponentY_internal_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
-- given
  (hint : ons_decInternalAdj d e) :
-- imply
  ((ons_decEdgeMicroDarts L d e).map (fun a => ons_dirExponentY a.2)).sum = 2 * (ons_dirExponentY e.2 - ons_dirExponentY d.2) := by
-- proof
  apply StatMech.Onsager.ons_decEdgeMicroDarts_sum_exponentY_internal L d e hint

/--
[ons_dirExponentX_dartRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_dirExponentX_dartRev_eq
  {L : ℕ}
  {d : ons_Dart L} :
-- imply
  ons_dirExponentX (ons_dartRev L d).2 = -ons_dirExponentX d.2 := by
-- proof
  apply StatMech.Onsager.ons_dirExponentX_dartRev L d

/--
[ons_dirExponentY_dartRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_dirExponentY_dartRev_eq
  {L : ℕ}
  {d : ons_Dart L} :
-- imply
  ons_dirExponentY (ons_dartRev L d).2 = -ons_dirExponentY d.2 := by
-- proof
  apply StatMech.Onsager.ons_dirExponentY_dartRev L d

/--
[ons_decExpandedDartList_sum_exponentX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedDartList_sum_exponentX_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v} :
-- imply
  ((ons_decExpandedDartList L p).map (fun a => ons_dirExponentX a.2)).sum = 2 * (ons_dirExponentX v.2 - ons_dirExponentX u.2) + 8 * ((ons_decWalkExternalDarts p).map (fun a => ons_dirExponentX a.2)).sum := by
-- proof
  apply StatMech.Onsager.ons_decExpandedDartList_sum_exponentX L p

/--
[ons_decExpandedDartList_sum_exponentY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedDartList_sum_exponentY_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v} :
-- imply
  ((ons_decExpandedDartList L p).map (fun a => ons_dirExponentY a.2)).sum = 2 * (ons_dirExponentY v.2 - ons_dirExponentY u.2) + 8 * ((ons_decWalkExternalDarts p).map (fun a => ons_dirExponentY a.2)).sum := by
-- proof
  apply StatMech.Onsager.ons_decExpandedDartList_sum_exponentY L p

/--
[ons_decWalkExternalDarts_sum_eq_cycleDartLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decWalkExternalDarts_sum_eq_cycleDartLoop_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {f : ons_Dart L → ℤ}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ((ons_decWalkExternalDarts q).map f).sum = ∑ k, f (ons_decCycleDartLoop q k) := by
-- proof
  apply StatMech.Onsager.ons_decWalkExternalDarts_sum_eq_cycleDartLoop q hq hsnd f

/--
[ons_decExpandedDartList_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedDartList_length_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v} :
-- imply
  (ons_decExpandedDartList L p).length = 4 * p.length := by
-- proof
  apply StatMech.Onsager.ons_decExpandedDartList_length L p

/--
[ons_decExpandedDartList_sites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedDartList_sites_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v} :
-- imply
  (ons_decExpandedDartList L p).map (fun a => a.1) = (ons_decEmbedWalk L p).support.dropLast := by
-- proof
  apply StatMech.Onsager.ons_decExpandedDartList_sites L p

/--
[ons_decExpandedDartList_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedDartList_edges_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v} :
-- imply
  (ons_decExpandedDartList L p).map (ons_portEdge (8 * L)) = (ons_decEmbedWalk L p).edges := by
-- proof
  apply StatMech.Onsager.ons_decExpandedDartList_edges L p

/--
[ons_decEdgeMicroDarts_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decEdgeMicroDarts_isChain_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
-- given
  (hde : (ons_decGraph L).Adj d e) :
-- imply
  List.IsChain (fun a b : ons_Dart (8 * L) => ons_dirStep (8 * L) a.2 a.1 = b.1) (ons_decEdgeMicroDarts L d e) := by
-- proof
  apply StatMech.Onsager.ons_decEdgeMicroDarts_isChain L d e hde

/--
[ons_decEdgeMicroDarts_last_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decEdgeMicroDarts_last_step_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
  {a : ons_Dart (8 * L)}
-- given
  (hde : (ons_decGraph L).Adj d e)
  (ha : a ∈ (ons_decEdgeMicroDarts L d e).getLast?) :
-- imply
  ons_dirStep (8 * L) a.2 a.1 = ons_decEmbedVertex L e := by
-- proof
  apply StatMech.Onsager.ons_decEdgeMicroDarts_last_step L d e hde ha

/--
[ons_decExpandedDartList_head_site](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedDartList_head_site_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v}
  {a : ons_Dart (8 * L)}
-- given
  (ha : a ∈ (ons_decExpandedDartList L p).head?) :
-- imply
  a.1 = ons_decEmbedVertex L u := by
-- proof
  apply StatMech.Onsager.ons_decExpandedDartList_head_site L p ha

/--
[ons_decExpandedDartList_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedDartList_isChain_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v} :
-- imply
  List.IsChain (fun a b : ons_Dart (8 * L) => ons_dirStep (8 * L) a.2 a.1 = b.1) (ons_decExpandedDartList L p) := by
-- proof
  apply StatMech.Onsager.ons_decExpandedDartList_isChain L p

/--
[ons_decExpandedDartList_last_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedDartList_last_step_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v}
  {a : ons_Dart (8 * L)}
-- given
  (ha : a ∈ (ons_decExpandedDartList L p).getLast?) :
-- imply
  ons_dirStep (8 * L) a.2 a.1 = ons_decEmbedVertex L v := by
-- proof
  apply StatMech.Onsager.ons_decExpandedDartList_last_step L p ha

/--
[ons_decExpandedRoot_site](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedRoot_site_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle) :
-- imply
  (ons_decExpandedRoot L q).1 = ons_decEmbedVertex L d := by
-- proof
  apply StatMech.Onsager.ons_decExpandedRoot_site L q hq

/--
[ons_decExpandedDartList_isChain_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedDartList_isChain_closed_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle) :
-- imply
  List.IsChain (fun a b : ons_Dart (8 * L) => ons_dirStep (8 * L) a.2 a.1 = b.1) (ons_decExpandedDartList L q ++ [ons_decExpandedRoot L q]) := by
-- proof
  apply StatMech.Onsager.ons_decExpandedDartList_isChain_closed L q hq

/--
[ons_decExpandedDartList_length_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedDartList_length_pos_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle) :
-- imply
  0 < (ons_decExpandedDartList L q).length := by
-- proof
  apply StatMech.Onsager.ons_decExpandedDartList_length_pos L q hq

/--
[ons_decExpandedGeometricLoop_sum_exponentX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedGeometricLoop_sum_exponentX_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d} :
-- imply
  ∑ k, ons_dirExponentX (ons_decExpandedGeometricLoop L q k).2 = 8 * ((ons_decWalkExternalDarts q).map (fun a => ons_dirExponentX a.2)).sum := by
-- proof
  apply StatMech.Onsager.ons_decExpandedGeometricLoop_sum_exponentX L q

/--
[ons_decExpandedGeometricLoop_sum_exponentY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedGeometricLoop_sum_exponentY_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d} :
-- imply
  ∑ k, ons_dirExponentY (ons_decExpandedGeometricLoop L q k).2 = 8 * ((ons_decWalkExternalDarts q).map (fun a => ons_dirExponentY a.2)).sum := by
-- proof
  apply StatMech.Onsager.ons_decExpandedGeometricLoop_sum_exponentY L q

/--
[ons_decExpandedGeometricLoop_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedGeometricLoop_edgeSet_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d} :
-- imply
  ons_dartEdgeSet (ons_decExpandedGeometricLoop L q) = (ons_decEmbedWalk L q).edges.toFinset := by
-- proof
  apply StatMech.Onsager.ons_decExpandedGeometricLoop_edgeSet L q

/--
[ons_decExpandedRoot_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedRoot_eq_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle) :
-- imply
  letI : NeZero (ons_decExpandedDartList L q).length := ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩ ons_decExpandedRoot L q = ons_decExpandedGeometricLoop L q 0 := by
-- proof
  apply StatMech.Onsager.ons_decExpandedRoot_eq_zero L q hq

/--
[ons_decExpandedGeometricLoop_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedGeometricLoop_valid_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle) :
-- imply
  letI : NeZero (ons_decExpandedDartList L q).length := ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩ ∀ k : Fin (ons_decExpandedDartList L q).length, ons_dirStep (8 * L) (ons_decExpandedGeometricLoop L q k).2 (ons_decExpandedGeometricLoop L q k).1 = (ons_decExpandedGeometricLoop L q (k + 1)).1 := by
-- proof
  apply StatMech.Onsager.ons_decExpandedGeometricLoop_valid L q hq

/--
[ons_decExpandedGeometricLoop_site_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedGeometricLoop_site_injective_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle) :
-- imply
  Function.Injective (fun k : Fin (ons_decExpandedDartList L q).length => (ons_decExpandedGeometricLoop L q k).1) := by
-- proof
  apply StatMech.Onsager.ons_decExpandedGeometricLoop_site_injective L q hq

/--
[ons_decExpandedKWLoop_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedKWLoop_edgeSet_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle) :
-- imply
  ons_dartEdgeSet (ons_decExpandedKWLoop L q hq) = (ons_decEmbedWalk L q).edges.toFinset := by
-- proof
  apply StatMech.Onsager.ons_decExpandedKWLoop_edgeSet L q hq

/--
[ons_decExpandedKWLoop_sum_exponentX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedKWLoop_sum_exponentX_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ∑ k, ons_dirExponentX (ons_decExpandedKWLoop L q hq k).2 = 8 * ∑ k, ons_dirExponentX (ons_decCycleDartLoop q k).2 := by
-- proof
  apply StatMech.Onsager.ons_decExpandedKWLoop_sum_exponentX L q hq hsnd

/--
[ons_decExpandedKWLoop_sum_exponentY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedKWLoop_sum_exponentY_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ∑ k, ons_dirExponentY (ons_decExpandedKWLoop L q hq k).2 = 8 * ∑ k, ons_dirExponentY (ons_decCycleDartLoop q k).2 := by
-- proof
  apply StatMech.Onsager.ons_decExpandedKWLoop_sum_exponentY L q hq hsnd

/--
[ons_decExpandedKWLoop_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedKWLoop_valid_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle) :
-- imply
  letI : NeZero (ons_decExpandedDartList L q).length := ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩ ∀ k : Fin (ons_decExpandedDartList L q).length, (ons_decExpandedKWLoop L q hq k).1 = ons_dirStep (8 * L) (ons_decExpandedKWLoop L q hq (k + 1)).2 (ons_decExpandedKWLoop L q hq (k + 1)).1 := by
-- proof
  apply StatMech.Onsager.ons_decExpandedKWLoop_valid L q hq

/--
[ons_decExpandedKWLoop_site_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedKWLoop_site_injective_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle) :
-- imply
  Function.Injective (fun k : Fin (ons_decExpandedDartList L q).length => (ons_decExpandedKWLoop L q hq k).1) := by
-- proof
  apply StatMech.Onsager.ons_decExpandedKWLoop_site_injective L q hq

/--
[ons_decExpandedKWLoop_site_mem_embedSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedKWLoop_site_mem_embedSupport_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {k : Fin (ons_decExpandedDartList L q).length}
-- given
  (hq : q.IsCycle) :
-- imply
  (ons_decExpandedKWLoop L q hq k).1 ∈ (ons_decEmbedWalk L q).support := by
-- proof
  apply StatMech.Onsager.ons_decExpandedKWLoop_site_mem_embedSupport L q hq k

/--
[ons_decExpandedKWLoop_sites_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedKWLoop_sites_disjoint_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {p : (ons_decGraph L).Walk e e}
-- given
  (hq : q.IsCycle)
  (hp : p.IsCycle)
  (hdisj : Disjoint q.toSubgraph.verts p.toSubgraph.verts) :
-- imply
  ∀ (i : Fin (ons_decExpandedDartList L q).length) (j : Fin (ons_decExpandedDartList L p).length), (ons_decExpandedKWLoop L q hq i).1 ≠ (ons_decExpandedKWLoop L p hp j).1 := by
-- proof
  apply StatMech.Onsager.ons_decExpandedKWLoop_sites_disjoint L q p hq hp hdisj

/--
[ons_decExpandedKWLoop_nonUturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpandedKWLoop_nonUturn_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle) :
-- imply
  letI : NeZero (ons_decExpandedDartList L q).length := ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩ ∀ k : Fin (ons_decExpandedDartList L q).length, (ons_decExpandedKWLoop L q hq k).2 ≠ (ons_decExpandedKWLoop L q hq (k + 1)).2 + 2 := by
-- proof
  apply StatMech.Onsager.ons_decExpandedKWLoop_nonUturn L q hq

/--
[ons_decEmbedWalk_evenHomology_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decEmbedWalk_evenHomology_eq_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ons_evenHomology (8 * L) (ons_decEmbedWalk L q).edges.toFinset = ons_evenHomology L (ons_walkOriginalEdges q) := by
-- proof
  apply StatMech.Onsager.ons_decEmbedWalk_evenHomology_eq L q hq hsnd

/--
[ons_decExpanded_turnProduct_eq_neg_one_of_zero_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean)
-/
@[path]
private lemma ons_decExpanded_turnProduct_eq_neg_one_of_zero_winding_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hx : ∑ k, ons_dirExponentX (ons_decExpandedKWLoop L q hq k).2 = 0)
  (hy : ∑ k, ons_dirExponentY (ons_decExpandedKWLoop L q hq k).2 = 0) :
-- imply
  letI : NeZero (ons_decExpandedDartList L q).length := ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩ ∏ k, ons_turnW ons_turnRoot (ons_decExpandedKWLoop L q hq (k + 1)).2 (ons_decExpandedKWLoop L q hq k).2 = -1 := by
-- proof
  apply StatMech.Onsager.ons_decExpanded_turnProduct_eq_neg_one_of_zero_winding L q hq hx hy


-- created on 2026-10-23
