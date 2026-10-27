import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopClassification.Part5
open StatMech StatMech.Onsager


/--
[ons_isPath_eq_of_edges_toFinset_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_isPath_eq_of_edges_toFinset_eq_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {p q : G.Walk u v}
-- given
  (hp : p.IsPath)
  (hq : q.IsPath)
  (hedges : p.edges.toFinset = q.edges.toFinset) :
-- imply
  p = q := by
-- proof
  apply StatMech.Onsager.ons_isPath_eq_of_edges_toFinset_eq p q hp hq hedges

/--
[ons_rooted_isCycle_eq_of_snd_edges_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_rooted_isCycle_eq_of_snd_edges_eq_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u : V}
  {p q : G.Walk u u}
-- given
  (hp : p.IsCycle)
  (hq : q.IsCycle)
  (hsnd : p.snd = q.snd)
  (hedges : p.edges.toFinset = q.edges.toFinset) :
-- imply
  p = q := by
-- proof
  apply StatMech.Onsager.ons_rooted_isCycle_eq_of_snd_edges_eq p q hp hq hsnd hedges

/--
[ons_decCycleDartList_copy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decCycleDartList_copy_eq
  {L : ℕ}
  {d e : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (h : d = e) :
-- imply
  ons_decCycleDartList (q.copy h h) = ons_decCycleDartList q := by
-- proof
  apply StatMech.Onsager.ons_decCycleDartList_copy q h

/--
[ons_squarefree_valid_loop_eq_of_zero_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_squarefree_valid_loop_eq_of_zero_eq_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {d e : Fin n → ons_Dart L}
  {S : Finset (ons_DecEdge L)}
-- given
  (hdvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hevalid : ∀ k : Fin n, (e k).1 = ons_dirStep L (e (k + 1)).2 (e (k + 1)).1)
  (hdexp : ons_decLoopExponent L d = ons_finsetExponent S)
  (heexp : ons_decLoopExponent L e = ons_finsetExponent S)
  (hzero : d 0 = e 0) :
-- imply
  d = e := by
-- proof
  apply StatMech.Onsager.ons_squarefree_valid_loop_eq_of_zero_eq L d e hdvalid hevalid S hdexp heexp hzero

/--
[ons_decChainPathIndices_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decChainPathIndices_comm_eq
  {a b : Fin 4} :
-- imply
  ons_decChainPathIndices a b = ons_decChainPathIndices b a := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_comm a b

/--
[ons_decLoopExponent_eq_external_add_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decLoopExponent_eq_external_add_internal_eq
  {L : ℕ}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L} :
-- imply
  ons_decLoopExponent L d = ons_decLoopExternalExponent L d + ons_decLoopInternalExponent L d := by
-- proof
  apply StatMech.Onsager.ons_decLoopExponent_eq_external_add_internal L d

/--
[ons_decLoopExponent_rotate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decLoopExponent_rotate_eq
  {L : ℕ}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
  {r : Fin n} :
-- imply
  ons_decLoopExponent L (ons_rotate r d) = ons_decLoopExponent L d := by
-- proof
  apply StatMech.Onsager.ons_decLoopExponent_rotate L d r

/--
[ons_decLoopScalar_rotate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decLoopScalar_rotate_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega u v : ℂ}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
  {r : Fin n} :
-- imply
  ons_decLoopScalar L omega u v (ons_rotate r d) = ons_decLoopScalar L omega u v d := by
-- proof
  apply StatMech.Onsager.ons_decLoopScalar_rotate L omega u v d r

/--
[ons_decLoopExternalExponent_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decLoopExternalExponent_loopRev_eq
  {L : ℕ}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L} :
-- imply
  ons_decLoopExternalExponent L (ons_loopRev L d) = ons_decLoopExternalExponent L d := by
-- proof
  apply StatMech.Onsager.ons_decLoopExternalExponent_loopRev L d

/--
[ons_decLoopInternalExponent_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decLoopInternalExponent_loopRev_eq
  {L : ℕ}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  ons_decLoopInternalExponent L (ons_loopRev L d) = ons_decLoopInternalExponent L d := by
-- proof
  apply StatMech.Onsager.ons_decLoopInternalExponent_loopRev L d hvalid

/--
[ons_decLoopExponent_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decLoopExponent_loopRev_eq
  {L : ℕ}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  ons_decLoopExponent L (ons_loopRev L d) = ons_decLoopExponent L d := by
-- proof
  apply StatMech.Onsager.ons_decLoopExponent_loopRev L d hvalid

/--
[ons_decLoopScalar_loopRev_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decLoopScalar_loopRev_spin_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L} :
-- imply
  ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (ons_loopRev L d) = ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d := by
-- proof
  apply StatMech.Onsager.ons_decLoopScalar_loopRev_spin L a b d

/--
[ons_mem_decSquarefreeLoopFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_mem_decSquarefreeLoopFinset_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  [NeZero n]
  {S : Finset (ons_DecEdge L)}
  {d : Fin n → ons_Dart L} :
-- imply
  d ∈ ons_decSquarefreeLoopFinset L a b S ↔ ons_decLoopExponent L d = ons_finsetExponent S ∧ ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d ≠ 0 := by
-- proof
  apply StatMech.Onsager.ons_mem_decSquarefreeLoopFinset L a b S d

/--
[ons_decSquarefreeLoop_eval_zero_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decSquarefreeLoop_eval_zero_injective_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  [NeZero n]
  {S : Finset (ons_DecEdge L)} :
-- imply
  Set.InjOn (fun d : Fin n → ons_Dart L ↦ d 0) (ons_decSquarefreeLoopFinset (n := n) L a b S : Set (Fin n → ons_Dart L)) := by
-- proof
  apply StatMech.Onsager.ons_decSquarefreeLoop_eval_zero_injective L a b S

/--
[ons_decLoop_portEdge_injective_of_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decLoop_portEdge_injective_of_squarefree_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
  {S : Finset (ons_DecEdge L)}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hexponent : ons_decLoopExponent L d = ons_finsetExponent S) :
-- imply
  Function.Injective (fun k : Fin n ↦ ons_portEdge L (d k)) := by
-- proof
  apply StatMech.Onsager.ons_decLoop_portEdge_injective_of_squarefree L d hvalid S hexponent

/--
[ons_decLoop_dart_ne_rev_of_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decLoop_dart_ne_rev_of_squarefree_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
  {S : Finset (ons_DecEdge L)}
  {i j : Fin n}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hexponent : ons_decLoopExponent L d = ons_finsetExponent S) :
-- imply
  d i ≠ ons_dartRev L (d j) := by
-- proof
  apply StatMech.Onsager.ons_decLoop_dart_ne_rev_of_squarefree L d hvalid S hexponent i j

/--
[ons_decLoopRootFinset_card_of_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decLoopRootFinset_card_of_squarefree_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
  {S : Finset (ons_DecEdge L)}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hexponent : ons_decLoopExponent L d = ons_finsetExponent S) :
-- imply
  (ons_decLoopRootFinset L d).card = 2 * n := by
-- proof
  apply StatMech.Onsager.ons_decLoopRootFinset_card_of_squarefree L d hvalid S hexponent

/--
[ons_decSquarefreeLoop_root_edge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decSquarefreeLoop_root_edge_mem_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  [NeZero n]
  {S : Finset (ons_DecEdge L)}
  {d : Fin n → ons_Dart L}
-- given
  (hd : d ∈ ons_decSquarefreeLoopFinset L a b S) :
-- imply
  s(d 0, ons_dartRev L (d 0)) ∈ S := by
-- proof
  apply StatMech.Onsager.ons_decSquarefreeLoop_root_edge_mem L a b S hd

/--
[ons_external_root_mem_decLoopRootFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_external_root_mem_decLoopRootFinset_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
  {S : Finset (ons_DecEdge L)}
  {root : ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hexponent : ons_decLoopExponent L d = ons_finsetExponent S)
  (hroot : s(root, ons_dartRev L root) ∈ S) :
-- imply
  root ∈ ons_decLoopRootFinset L d := by
-- proof
  apply StatMech.Onsager.ons_external_root_mem_decLoopRootFinset L d hvalid S hexponent root hroot

/--
[ons_decLoopOrientation_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decLoopOrientation_mem_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  [NeZero n]
  {S : Finset (ons_DecEdge L)}
  {d : Fin n → ons_Dart L}
  {orientation : Fin n ⊕ Fin n}
-- given
  (hd : d ∈ ons_decSquarefreeLoopFinset L a b S) :
-- imply
  ons_decLoopOrientation L d orientation ∈ ons_decSquarefreeLoopFinset L a b S := by
-- proof
  apply StatMech.Onsager.ons_decLoopOrientation_mem L a b S hd orientation

/--
[ons_decLoopOrientation_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decLoopOrientation_injective_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
  {S : Finset (ons_DecEdge L)}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hexponent : ons_decLoopExponent L d = ons_finsetExponent S) :
-- imply
  Function.Injective (ons_decLoopOrientation L d) := by
-- proof
  apply StatMech.Onsager.ons_decLoopOrientation_injective L d hvalid S hexponent

/--
[ons_decSquarefreeLoopFinset_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decSquarefreeLoopFinset_card_le_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  [NeZero n]
  {S : Finset (ons_DecEdge L)}
  {d : Fin n → ons_Dart L}
-- given
  (hd : d ∈ ons_decSquarefreeLoopFinset (n := n) L a b S) :
-- imply
  (ons_decSquarefreeLoopFinset (n := n) L a b S).card ≤ 2 * n := by
-- proof
  apply StatMech.Onsager.ons_decSquarefreeLoopFinset_card_le L a b S hd

/--
[ons_decSquarefreeLoopFinset_card_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decSquarefreeLoopFinset_card_ge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  [NeZero n]
  {S : Finset (ons_DecEdge L)}
  {d : Fin n → ons_Dart L}
-- given
  (hd : d ∈ ons_decSquarefreeLoopFinset (n := n) L a b S) :
-- imply
  2 * n ≤ (ons_decSquarefreeLoopFinset (n := n) L a b S).card := by
-- proof
  apply StatMech.Onsager.ons_decSquarefreeLoopFinset_card_ge L a b S hd

/--
[ons_decSquarefreeLoopFinset_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decSquarefreeLoopFinset_card_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  [NeZero n]
  {S : Finset (ons_DecEdge L)}
  {d : Fin n → ons_Dart L}
-- given
  (hd : d ∈ ons_decSquarefreeLoopFinset (n := n) L a b S) :
-- imply
  (ons_decSquarefreeLoopFinset (n := n) L a b S).card = 2 * n := by
-- proof
  apply StatMech.Onsager.ons_decSquarefreeLoopFinset_card L a b S hd

/--
[ons_decLoopRootFinset_mem_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decLoopRootFinset_mem_external_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
  {S : Finset (ons_DecEdge L)}
  {root : ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hexponent : ons_decLoopExponent L d = ons_finsetExponent S) :
-- imply
  root ∈ ons_decLoopRootFinset L d ↔ s(root, ons_dartRev L root) ∈ S := by
-- proof
  apply StatMech.Onsager.ons_decLoopRootFinset_mem_external L d hvalid S hexponent root

/--
[ons_decSquarefreeLoop_length_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decSquarefreeLoop_length_unique_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n m : ℕ}
  [NeZero n]
  [NeZero m]
  {S : Finset (ons_DecEdge L)}
  {d : Fin n → ons_Dart L}
  {e : Fin m → ons_Dart L}
-- given
  (hd : d ∈ ons_decSquarefreeLoopFinset L a b S)
  (he : e ∈ ons_decSquarefreeLoopFinset L a b S) :
-- imply
  n = m := by
-- proof
  apply StatMech.Onsager.ons_decSquarefreeLoop_length_unique L a b S hd he

/--
[ons_walkOriginalEdges_eq_of_edges_toFinset_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_walkOriginalEdges_eq_of_edges_toFinset_eq_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u u}
  {q : (ons_decGraph L).Walk v v}
-- given
  (hedges : p.edges.toFinset = q.edges.toFinset) :
-- imply
  ons_walkOriginalEdges p = ons_walkOriginalEdges q := by
-- proof
  apply StatMech.Onsager.ons_walkOriginalEdges_eq_of_edges_toFinset_eq p q hedges

/--
[ons_decSquarefreeLoop_scalar_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decSquarefreeLoop_scalar_eq_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n m : ℕ}
  [NeZero n]
  [NeZero m]
  {S : Finset (ons_DecEdge L)}
  {d : Fin n → ons_Dart L}
  {e : Fin m → ons_Dart L}
-- given
  (hd : d ∈ ons_decSquarefreeLoopFinset L a b S)
  (he : e ∈ ons_decSquarefreeLoopFinset L a b S) :
-- imply
  ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d = ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) e := by
-- proof
  apply StatMech.Onsager.ons_decSquarefreeLoop_scalar_eq L a b S hd he

/--
[ons_decSquarefreeLoop_bucket_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decSquarefreeLoop_bucket_sum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  [NeZero n]
  {S : Finset (ons_DecEdge L)}
  {d : Fin n → ons_Dart L}
-- given
  (hd : d ∈ ons_decSquarefreeLoopFinset L a b S) :
-- imply
  (∑ e : Fin n → ons_Dart L, if ons_decLoopExponent L e = ons_finsetExponent S then ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) e else 0) = (2 * n : ℂ) * ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d := by
-- proof
  apply StatMech.Onsager.ons_decSquarefreeLoop_bucket_sum L a b S hd

/--
[ons_decFormalLogCoeff_squarefree_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decFormalLogCoeff_squarefree_of_mem_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {S : Finset (ons_DecEdge L)}
  {r : ℕ}
  {d : Fin (r + 1) → ons_Dart L}
-- given
  (hd : d ∈ ons_decSquarefreeLoopFinset L a b S) :
-- imply
  ons_decFormalLogCoeff L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (ons_finsetExponent S) = (ons_spinCharacter a b (ons_evenHomology L (ons_walkOriginalEdges (ons_decLoopWalk L d (ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d ((ons_mem_decSquarefreeLoopFinset L a b S d).mp hd).2)))) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decFormalLogCoeff_squarefree_of_mem L a b S r d hd

/--
[ons_decFormalLogCoeff_squarefree_eq_zero_of_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decFormalLogCoeff_squarefree_eq_zero_of_empty_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {S : Finset (ons_DecEdge L)}
-- given
  (hempty : ∀ r : ℕ, (ons_decSquarefreeLoopFinset (n := r + 1) L a b S).Nonempty → False) :
-- imply
  ons_decFormalLogCoeff L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (ons_finsetExponent S) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalLogCoeff_squarefree_eq_zero_of_empty L a b S hempty

/--
[ons_decFormalLogCoeff_squarefree_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decFormalLogCoeff_squarefree_cases_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {S : Finset (ons_DecEdge L)} :
-- imply
  ons_decFormalLogCoeff L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (ons_finsetExponent S) = 0 ∨ ∃ (r : ℕ) (d : Fin (r + 1) → ons_Dart L) (hd : d ∈ ons_decSquarefreeLoopFinset L a b S), ons_decFormalLogCoeff L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (ons_finsetExponent S) = (ons_spinCharacter a b (ons_evenHomology L (ons_walkOriginalEdges (ons_decLoopWalk L d (ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d ((ons_mem_decSquarefreeLoopFinset L a b S d).mp hd).2)))) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decFormalLogCoeff_squarefree_cases L a b S

/--
[ons_decSquarefreeLoop_edges_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean)
-/
@[path]
private lemma ons_decSquarefreeLoop_edges_even_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  [NeZero n]
  {S : Finset (ons_DecEdge L)}
  {d : Fin n → ons_Dart L}
-- given
  (hd : d ∈ ons_decSquarefreeLoopFinset L a b S) :
-- imply
  S ∈ StatMech.Ising.evenSubgraphs (ons_decGraph L) := by
-- proof
  apply StatMech.Onsager.ons_decSquarefreeLoop_edges_even L a b S hd


-- created on 2026-10-23
