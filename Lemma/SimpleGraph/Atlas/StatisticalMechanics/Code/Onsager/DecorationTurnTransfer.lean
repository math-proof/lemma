import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.DecorationTurnTransfer
open StatMech StatMech.Onsager


/--
[ons_internalMicroDirections_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_internalMicroDirections_turn_eq
  {a : Fin 4}
  {ports : List (Fin 4)}
-- given
  (hne : ports ≠ [])
  (hhead : ports.head? = some (a + 2))
  (hchain : List.IsChain ons_portLineAdj ports)
  (hnodup : ports.Nodup) :
-- imply
  let dirs := List.replicate 4 a ++ ons_internalMicroDirections ports ons_openTurnSum dirs + ons_turnPow dirs.getLast! ports.getLast! = ons_turnPow a ports.getLast! := by
-- proof
  apply StatMech.Onsager.ons_internalMicroDirections_turn a ports hne hhead hchain hnodup

/--
[ons_decEdgeMicroDarts_directions_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_decEdgeMicroDarts_directions_external_eq
  {L : ℕ}
  {d e : ons_Dart L}
-- given
  (hrev : e = ons_dartRev L d) :
-- imply
  (ons_decEdgeMicroDarts L d e).map (fun a ↦ a.2) = List.replicate 4 d.2 := by
-- proof
  apply StatMech.Onsager.ons_decEdgeMicroDarts_directions_external L d e hrev

/--
[ons_decEdgeMicroDarts_directions_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_decEdgeMicroDarts_directions_internal_eq
  {L : ℕ}
  {d e : ons_Dart L}
-- given
  (hint : ons_decInternalAdj d e) :
-- imply
  (ons_decEdgeMicroDarts L d e).map (fun a ↦ a.2) = [e.2, e.2, d.2 + 2, d.2 + 2] := by
-- proof
  apply StatMech.Onsager.ons_decEdgeMicroDarts_directions_internal L d e hint

/--
[ons_walk_support_eq_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_walk_support_eq_cons_eq
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v} :
-- imply
  p.support = u :: p.support.tail := by
-- proof
  apply StatMech.Onsager.ons_walk_support_eq_cons p

/--
[ons_decExpanded_internal_directions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_decExpanded_internal_directions_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v}
-- given
  (hint : ∀ a ∈ p.darts, ons_decInternalAdj a.fst a.snd) :
-- imply
  (ons_decExpandedDartList L p).map (fun a ↦ a.2) = ons_internalMicroDirections (p.support.map (fun a ↦ a.2)) := by
-- proof
  apply StatMech.Onsager.ons_decExpanded_internal_directions L p hint

/--
[ons_support_directions_isChain_portLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_support_directions_isChain_portLine_eq
  {L : ℕ}
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v}
-- given
  (hint : ∀ a ∈ p.darts, ons_decInternalAdj a.fst a.snd) :
-- imply
  List.IsChain ons_portLineAdj (p.support.map (fun a ↦ a.2)) := by
-- proof
  apply StatMech.Onsager.ons_support_directions_isChain_portLine p hint

/--
[ons_internalWalk_support_site](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_internalWalk_support_site_eq
  {L : ℕ}
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v}
-- given
  (hint : ∀ a ∈ p.darts, ons_decInternalAdj a.fst a.snd) :
-- imply
  ∀ a ∈ p.support, a.1 = u.1 := by
-- proof
  apply StatMech.Onsager.ons_internalWalk_support_site p hint

/--
[ons_internalWalk_refined_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_internalWalk_refined_turn_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {v : ons_Dart L}
  {p : (ons_decGraph L).Walk (ons_dartRev L d) v}
-- given
  (hint : ∀ a ∈ p.darts, ons_decInternalAdj a.fst a.snd)
  (hpath : p.IsPath) :
-- imply
  let dirs := List.replicate 4 d.2 ++ (ons_decExpandedDartList L p).map (fun a ↦ a.2) ons_openTurnSum dirs + ons_turnPow dirs.getLast! v.2 = ons_turnPow d.2 v.2 := by
-- proof
  apply StatMech.Onsager.ons_internalWalk_refined_turn L d p hint hpath

/--
[ons_walkExpandedDirections_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_walkExpandedDirections_nil_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u : ons_Dart L} :
-- imply
  ons_walkExpandedDirections L (SimpleGraph.Walk.nil : (ons_decGraph L).Walk u u) = [] := by
-- proof
  apply StatMech.Onsager.ons_walkExpandedDirections_nil L u

/--
[ons_walkExternalDirections_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_walkExternalDirections_nil_eq
  {L : ℕ}
  {u : ons_Dart L} :
-- imply
  ons_walkExternalDirections (SimpleGraph.Walk.nil : (ons_decGraph L).Walk u u) = [] := by
-- proof
  apply StatMech.Onsager.ons_walkExternalDirections_nil L u

/--
[ons_walkExpandedDirections_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_walkExpandedDirections_append_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v w : ons_Dart L}
  {p : (ons_decGraph L).Walk u v}
  {q : (ons_decGraph L).Walk v w} :
-- imply
  ons_walkExpandedDirections L (p.append q) = ons_walkExpandedDirections L p ++ ons_walkExpandedDirections L q := by
-- proof
  apply StatMech.Onsager.ons_walkExpandedDirections_append L p q

/--
[ons_walkExpandedDirections_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_walkExpandedDirections_cons_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v w : ons_Dart L}
  {p : (ons_decGraph L).Walk v w}
-- given
  (h : (ons_decGraph L).Adj u v) :
-- imply
  ons_walkExpandedDirections L (SimpleGraph.Walk.cons h p) = (ons_decEdgeMicroDarts L u v).map (fun a ↦ a.2) ++ ons_walkExpandedDirections L p := by
-- proof
  apply StatMech.Onsager.ons_walkExpandedDirections_cons L h p

/--
[ons_decTurnTransfer_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_decTurnTransfer_invariant_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {u v : ons_Dart L}
  {r : (ons_decGraph L).Walk (ons_dartRev L d) u}
  {p : (ons_decGraph L).Walk u v}
-- given
  (hrint : ∀ a ∈ r.darts, ons_decInternalAdj a.fst a.snd)
  (hrpath : r.IsPath)
  (hallpath : (r.append p).IsPath) :
-- imply
  let full := List.replicate 4 d.2 ++ ons_walkExpandedDirections L r ++ ons_walkExpandedDirections L p let ext := d.2 :: ons_walkExternalDirections p ons_openTurnSum full + ons_turnPow full.getLast! v.2 = ons_openTurnSum ext + ons_turnPow ext.getLast! v.2 := by
-- proof
  apply StatMech.Onsager.ons_decTurnTransfer_invariant L d r p hrint hrpath hallpath

/--
[ons_decExpanded_geometric_cyclicTurnSum_eq_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_decExpanded_geometric_cyclicTurnSum_eq_external_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ons_cyclicTurnSum ((ons_decExpandedDartList L q).map (fun a ↦ a.2)) = ons_cyclicTurnSum ((ons_decWalkExternalDarts q).map (fun a ↦ a.2)) := by
-- proof
  apply StatMech.Onsager.ons_decExpanded_geometric_cyclicTurnSum_eq_external L q hq hsnd

/--
[ons_ofFn_neg_get_cons_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_ofFn_neg_get_cons_reverse_eq
  {x : X}
  {xs : List X} :
-- imply
  List.ofFn (fun k : Fin (x :: xs.reverse).length ↦ (x :: xs.reverse).get (-k)) = x :: xs := by
-- proof
  apply StatMech.Onsager.ons_ofFn_neg_get_cons_reverse x xs

/--
[ons_decCycleDartLoop_liftDir_ofFn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_decCycleDartLoop_liftDir_ofFn_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  List.ofFn (ons_liftDir (ons_decCycleDartLoop q)) = (ons_decWalkExternalDarts q).map (fun a ↦ a.2) := by
-- proof
  apply StatMech.Onsager.ons_decCycleDartLoop_liftDir_ofFn L q hq hsnd

/--
[ons_decExpandedKWLoop_liftDir_ofFn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_decExpandedKWLoop_liftDir_ofFn_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle) :
-- imply
  letI : NeZero (ons_decExpandedDartList L q).length := ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩ List.ofFn (ons_liftDir (ons_decExpandedKWLoop L q hq)) = (ons_decExpandedDartList L q).map (fun a ↦ a.2) := by
-- proof
  apply StatMech.Onsager.ons_decExpandedKWLoop_liftDir_ofFn L q hq

/--
[ons_nonUturn_of_valid_portEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_nonUturn_of_valid_portEdge_injective_eq
  {L n : ℕ}
  [NeZero n]
  {v : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hinj : Function.Injective (fun k ↦ ons_portEdge L (v k))) :
-- imply
  ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2 := by
-- proof
  apply StatMech.Onsager.ons_nonUturn_of_valid_portEdge_injective v hvalid hinj

/--
[ons_turnProduct_eq_zpow_cyclic_liftDir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_turnProduct_eq_zpow_cyclic_liftDir_eq
  {L n : ℕ}
  [NeZero n]
  {omega : ℂ}
  {v : Fin n → ons_Dart L}
-- given
  (homega : omega ≠ 0)
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2) :
-- imply
  (∏ k, ons_turnW omega (v (k + 1)).2 (v k).2) = omega ^ ons_cyclicTurnSum (List.ofFn (ons_liftDir v)) := by
-- proof
  apply StatMech.Onsager.ons_turnProduct_eq_zpow_cyclic_liftDir omega homega v hnu

/--
[ons_decCycleDartLoop_nonUturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_decCycleDartLoop_nonUturn_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ∀ k : Fin (ons_decCycleDartList q).length, (ons_decCycleDartLoop q k).2 ≠ (ons_decCycleDartLoop q (k + 1)).2 + 2 := by
-- proof
  apply StatMech.Onsager.ons_decCycleDartLoop_nonUturn L q hq hsnd

/--
[ons_decCycle_turnProduct_eq_expanded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_decCycle_turnProduct_eq_expanded_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  letI : NeZero (ons_decExpandedDartList L q).length := ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩ (∏ k, ons_turnW ons_turnRoot (ons_decCycleDartLoop q (k + 1)).2 (ons_decCycleDartLoop q k).2) = ∏ k, ons_turnW ons_turnRoot (ons_decExpandedKWLoop L q hq (k + 1)).2 (ons_decExpandedKWLoop L q hq k).2 := by
-- proof
  apply StatMech.Onsager.ons_decCycle_turnProduct_eq_expanded L q hq hsnd

/--
[ons_decExpanded_winding_eq_zero_of_zeroHomology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_decExpanded_winding_eq_zero_of_zeroHomology_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d)
  (hhom : ons_evenHomology L (ons_walkOriginalEdges q) = 0) :
-- imply
  letI : NeZero (ons_decExpandedDartList L q).length := ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩ (∑ k, ons_dirExponentX (ons_decExpandedKWLoop L q hq k).2) = 0 ∧ (∑ k, ons_dirExponentY (ons_decExpandedKWLoop L q hq k).2) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decExpanded_winding_eq_zero_of_zeroHomology L q hq hsnd hhom

/--
[ons_neg_spinCharacter_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_neg_spinCharacter_zero_zero_eq
-- given
  (h : Fin 2 × Fin 2) :
-- imply
  -(ons_spinCharacter 0 0 h : ℂ) = if h = 0 then -1 else 1 := by
-- proof
  apply StatMech.Onsager.ons_neg_spinCharacter_zero_zero h

/--
[ons_decCycle_turnProduct_eq_neg_spinCharacter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean)
-/
@[path]
private lemma ons_decCycle_turnProduct_eq_neg_spinCharacter_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  (∏ k, ons_turnW ons_turnRoot (ons_decCycleDartLoop q (k + 1)).2 (ons_decCycleDartLoop q k).2) = -(ons_spinCharacter 0 0 (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decCycle_turnProduct_eq_neg_spinCharacter L q hq hsnd


-- created on 2026-10-23
