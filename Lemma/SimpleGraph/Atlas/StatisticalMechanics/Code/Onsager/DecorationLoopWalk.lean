import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part7
open StatMech StatMech.Onsager


/--
[ons_walk_count_incident_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_walk_count_incident_edges_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
  {x : V} :
-- imply
  p.edges.countP (fun edge ↦ x ∈ edge) = p.support.dropLast.count x + p.support.tail.count x := by
-- proof
  apply StatMech.Onsager.ons_walk_count_incident_edges p x

/--
[ons_closed_walk_count_incident_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_closed_walk_count_incident_edges_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u : V}
  {p : G.Walk u u}
  {x : V} :
-- imply
  p.edges.countP (fun edge ↦ x ∈ edge) = 2 * p.support.tail.count x := by
-- proof
  apply StatMech.Onsager.ons_closed_walk_count_incident_edges p x

/--
[ons_trail_count_incident_edges_le_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_trail_count_incident_edges_le_degree_eq
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u v : V}
  {p : G.Walk u v}
  {x : V}
-- given
  (hp : p.IsTrail) :
-- imply
  p.edges.countP (fun edge ↦ x ∈ edge) ≤ G.degree x := by
-- proof
  apply StatMech.Onsager.ons_trail_count_incident_edges_le_degree G hp x

/--
[ons_closed_trail_isCycle_of_degree_le_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_closed_trail_isCycle_of_degree_le_three_eq
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u : V}
  {p : G.Walk u u}
-- given
  (hp : p.IsTrail)
  (hne : p ≠ .nil)
  (hdeg : ∀ v, G.degree v ≤ 3) :
-- imply
  p.IsCycle := by
-- proof
  apply StatMech.Onsager.ons_closed_trail_isCycle_of_degree_le_three G p hp hne hdeg

/--
[ons_decWalkExternalDarts_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decWalkExternalDarts_append_eq
  {L : ℕ}
  {u v w : ons_Dart L}
  {p : (ons_decGraph L).Walk u v}
  {q : (ons_decGraph L).Walk v w} :
-- imply
  ons_decWalkExternalDarts (p.append q) = ons_decWalkExternalDarts p ++ ons_decWalkExternalDarts q := by
-- proof
  apply StatMech.Onsager.ons_decWalkExternalDarts_append p q

/--
[ons_decPortChainPath_externalDarts_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decPortChainPath_externalDarts_eq_nil_eq
  {L : ℕ}
  [Fact (2 < L)]
  {site : ZMod L × ZMod L}
  {a b : Fin 4} :
-- imply
  ons_decWalkExternalDarts (ons_decPortChainPath L site a b) = [] := by
-- proof
  apply StatMech.Onsager.ons_decPortChainPath_externalDarts_eq_nil L site a b

/--
[ons_decTransitionWalk_externalDarts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decTransitionWalk_externalDarts_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d₂ d₁ : ons_Dart L}
-- given
  (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
-- imply
  ons_decWalkExternalDarts (ons_decTransitionWalk L d₂ d₁ hstep) = [d₁] := by
-- proof
  apply StatMech.Onsager.ons_decTransitionWalk_externalDarts L d₂ d₁ hstep

/--
[ons_finsetExponent_toFinset_eq_edgeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_finsetExponent_toFinset_eq_edgeCount_eq
  [DecidableEq E]
  {l : List E}
-- given
  (hl : l.Nodup) :
-- imply
  ons_finsetExponent l.toFinset = Multiset.toFinsupp (l : Multiset E) := by
-- proof
  apply StatMech.Onsager.ons_finsetExponent_toFinset_eq_edgeCount l hl

/--
[ons_decTransitionExponent_eq_edgeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decTransitionExponent_eq_edgeCount_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d₂ d₁ : ons_Dart L}
-- given
  (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
-- imply
  ons_decTransitionExponent L d₂ d₁ = ons_decWalkEdgeCount (ons_decTransitionWalk L d₂ d₁ hstep) := by
-- proof
  apply StatMech.Onsager.ons_decTransitionExponent_eq_edgeCount L d₂ d₁ hstep

/--
[ons_decKWChainExponent_eq_zipWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decKWChainExponent_eq_zipWith_eq
  {L : ℕ}
  {start : ons_Dart L}
  {tail : List (ons_Dart L)} :
-- imply
  ons_decKWChainExponent L start tail = (List.zipWith (fun source target ↦ ons_decTransitionExponent L target source) (start :: tail) tail).sum := by
-- proof
  apply StatMech.Onsager.ons_decKWChainExponent_eq_zipWith L start tail

/--
[ons_isChain_closed_ofFn_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_isChain_closed_ofFn_mk_eq
  {R : alpha → alpha → Prop}
  {n : ℕ}
  [NeZero n]
  {f : Fin n → alpha}
-- given
  (hstep : ∀ k : Fin n, R (f k) (f (k + 1))) :
-- imply
  List.IsChain R (List.ofFn f ++ [f 0]) := by
-- proof
  apply StatMech.Onsager.ons_isChain_closed_ofFn_mk f hstep

/--
[ons_decKWChainLast_append_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decKWChainLast_append_singleton_eq
  {start : ons_Dart L}
  {tail : List (ons_Dart L)}
  {finish : ons_Dart L} :
-- imply
  ons_decKWChainLast start (tail ++ [finish]) = finish := by
-- proof
  apply StatMech.Onsager.ons_decKWChainLast_append_singleton start tail finish

/--
[ons_decWalkOfKWChain_edgeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decWalkOfKWChain_edgeCount_eq
  {L : ℕ}
  [Fact (2 < L)]
  {start : ons_Dart L}
  {tail : List (ons_Dart L)}
-- given
  (hchain : List.IsChain (ons_decGeometricStep L) (start :: tail)) :
-- imply
  ons_decWalkEdgeCount (ons_decWalkOfKWChain L start tail hchain) = ons_decKWChainExponent L start tail := by
-- proof
  apply StatMech.Onsager.ons_decWalkOfKWChain_edgeCount L start tail hchain

/--
[ons_decWalkOfKWChain_externalDarts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decWalkOfKWChain_externalDarts_eq
  {L : ℕ}
  [Fact (2 < L)]
  {start : ons_Dart L}
  {tail : List (ons_Dart L)}
-- given
  (hchain : List.IsChain (ons_decGeometricStep L) (start :: tail)) :
-- imply
  ons_decWalkExternalDarts (ons_decWalkOfKWChain L start tail hchain) = (start :: tail).dropLast := by
-- proof
  apply StatMech.Onsager.ons_decWalkOfKWChain_externalDarts L start tail hchain

/--
[ons_decWalkOfKWChain_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decWalkOfKWChain_snd_eq
  {L : ℕ}
  {start target : ons_Dart L}
  {rest : List (ons_Dart L)}
-- given
  (hchain : List.IsChain (ons_decGeometricStep L) (start :: target :: rest)) :
-- imply
  (ons_decWalkOfKWChain L start (target :: rest) hchain).snd = ons_dartRev L start := by
-- proof
  apply StatMech.Onsager.ons_decWalkOfKWChain_snd L start target rest hchain

/--
[ons_decWalkOfKWChain_snd_of_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decWalkOfKWChain_snd_of_ne_nil_eq
  {L : ℕ}
  {start : ons_Dart L}
  {tail : List (ons_Dart L)}
-- given
  (hchain : List.IsChain (ons_decGeometricStep L) (start :: tail))
  (htail : tail ≠ []) :
-- imply
  (ons_decWalkOfKWChain L start tail hchain).snd = ons_dartRev L start := by
-- proof
  apply StatMech.Onsager.ons_decWalkOfKWChain_snd_of_ne_nil L start tail hchain htail

/--
[ons_decKWChainExponent_closed_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decKWChainExponent_closed_eq_sum_eq
  {L : ℕ}
  {n : ℕ}
  [NeZero n]
  {f : Fin n → ons_Dart L} :
-- imply
  let states := List.ofFn f ons_decKWChainExponent L (f 0) (states.tail ++ [f 0]) = ∑ k : Fin n, ons_decTransitionExponent L (f (k + 1)) (f k) := by
-- proof
  apply StatMech.Onsager.ons_decKWChainExponent_closed_eq_sum L f

/--
[ons_decGeometricLoopStates_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decGeometricLoopStates_valid_eq
  {L n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  ∀ k : Fin n, ons_decGeometricStep L (ons_decGeometricLoopStates d k) (ons_decGeometricLoopStates d (k + 1)) := by
-- proof
  apply StatMech.Onsager.ons_decGeometricLoopStates_valid d hvalid

/--
[ons_decGeometricLoopStates_sum_exponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decGeometricLoopStates_sum_exponent_eq
  {L n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L} :
-- imply
  (∑ k : Fin n, ons_decTransitionExponent L (ons_decGeometricLoopStates d (k + 1)) (ons_decGeometricLoopStates d k)) = ons_decLoopExponent L d := by
-- proof
  apply StatMech.Onsager.ons_decGeometricLoopStates_sum_exponent d

/--
[ons_list_reverse_ofFn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_list_reverse_ofFn_eq
  {n : ℕ}
  {f : Fin n → alpha} :
-- imply
  (List.ofFn f).reverse = List.ofFn (fun i ↦ f i.rev) := by
-- proof
  apply StatMech.Onsager.ons_list_reverse_ofFn f

/--
[ons_decGeometricLoopStates_tail_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decGeometricLoopStates_tail_reverse_eq
  {L n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L} :
-- imply
  d 0 :: (List.ofFn (ons_decGeometricLoopStates d)).tail.reverse = List.ofFn d := by
-- proof
  apply StatMech.Onsager.ons_decGeometricLoopStates_tail_reverse d

/--
[ons_decLoopWalk_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decLoopWalk_snd_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  (ons_decLoopWalk L d hvalid).snd = ons_dartRev L (d 0) := by
-- proof
  apply StatMech.Onsager.ons_decLoopWalk_snd L d hvalid

/--
[ons_decLoopWalk_externalDarts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decLoopWalk_externalDarts_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  ons_decWalkExternalDarts (ons_decLoopWalk L d hvalid) = List.ofFn (ons_decGeometricLoopStates d) := by
-- proof
  apply StatMech.Onsager.ons_decLoopWalk_externalDarts L d hvalid

/--
[ons_decLoopWalk_cycleDartList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decLoopWalk_cycleDartList_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  ons_decCycleDartList (ons_decLoopWalk L d hvalid) = List.ofFn d := by
-- proof
  apply StatMech.Onsager.ons_decLoopWalk_cycleDartList L d hvalid

/--
[ons_decLoopWalk_cycleDartLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decLoopWalk_cycleDartLoop_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
  {k : Fin n}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  ons_decCycleDartLoop (ons_decLoopWalk L d hvalid) ⟨k.val, by rw [ons_decLoopWalk_cycleDartList, List.length_ofFn] exact k.isLt⟩ = d k := by
-- proof
  apply StatMech.Onsager.ons_decLoopWalk_cycleDartLoop L d hvalid k

/--
[ons_decLoopWalk_edgeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decLoopWalk_edgeCount_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  ons_decWalkEdgeCount (ons_decLoopWalk L d hvalid) = ons_decLoopExponent L d := by
-- proof
  apply StatMech.Onsager.ons_decLoopWalk_edgeCount L d hvalid

/--
[ons_decLoopWalk_isTrail_of_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decLoopWalk_isTrail_of_squarefree_eq
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
  (ons_decLoopWalk L d hvalid).IsTrail := by
-- proof
  apply StatMech.Onsager.ons_decLoopWalk_isTrail_of_squarefree L d hvalid S hexponent

/--
[ons_decLoopWalk_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decLoopWalk_ne_nil_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  ons_decLoopWalk L d hvalid ≠ .nil := by
-- proof
  apply StatMech.Onsager.ons_decLoopWalk_ne_nil L d hvalid

/--
[ons_decLoopWalk_isCycle_of_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decLoopWalk_isCycle_of_squarefree_eq
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
  (ons_decLoopWalk L d hvalid).IsCycle := by
-- proof
  apply StatMech.Onsager.ons_decLoopWalk_isCycle_of_squarefree L d hvalid S hexponent

/--
[ons_decLoopWalk_edges_toFinset_of_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decLoopWalk_edges_toFinset_of_squarefree_eq
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
  (ons_decLoopWalk L d hvalid).edges.toFinset = S := by
-- proof
  apply StatMech.Onsager.ons_decLoopWalk_edges_toFinset_of_squarefree L d hvalid S hexponent

/--
[ons_decLoop_valid_of_scalar_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decLoop_valid_of_scalar_ne_zero_eq
  {L : ℕ}
  {omega u v : ℂ}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hscalar : ons_decLoopScalar L omega u v d ≠ 0) :
-- imply
  ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1 := by
-- proof
  apply StatMech.Onsager.ons_decLoop_valid_of_scalar_ne_zero L omega u v d hscalar

/--
[ons_decLoopScalar_eq_loopWeight_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decLoopScalar_eq_loopWeight_one_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega u v : ℂ}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L} :
-- imply
  ons_decLoopScalar L omega u v d = ons_loopWeight (ons_KWmatWeightedPhase L (fun _ ↦ 1) omega u v) d := by
-- proof
  apply StatMech.Onsager.ons_decLoopScalar_eq_loopWeight_one L omega u v d

/--
[ons_decLoopScalar_eq_cycleFirstReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decLoopScalar_eq_cycleFirstReturn_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega u v : ℂ}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  ons_decLoopScalar L omega u v d = ons_edgeWeight (ons_KWmatWeightedPhase L (fun _ ↦ 1) omega u v) (ons_decCycleFirstReturn (ons_decLoopWalk L d hvalid)) := by
-- proof
  apply StatMech.Onsager.ons_decLoopScalar_eq_cycleFirstReturn L omega u v d hvalid

/--
[ons_decLoopScalar_eq_neg_spinCharacter_of_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean)
-/
@[path]
private lemma ons_decLoopScalar_eq_neg_spinCharacter_of_squarefree_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
  {S : Finset (ons_DecEdge L)}
-- given
  (hexponent : ons_decLoopExponent L d = ons_finsetExponent S)
  (hscalar : ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d ≠ 0) :
-- imply
  ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d = -((ons_spinCharacter a b (ons_evenHomology L (ons_walkOriginalEdges (ons_decLoopWalk L d (ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d hscalar))))) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decLoopScalar_eq_neg_spinCharacter_of_squarefree L a b d S hexponent hscalar


-- created on 2026-10-23
