import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.DecorationCycleExponent
open StatMech StatMech.Onsager


/--
[ons_portLine_isTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean)
-/
@[path]
private lemma ons_portLine_isTree_eq :
-- imply
  (SimpleGraph.pathGraph 4).IsTree := by
-- proof
  apply StatMech.Onsager.ons_portLine_isTree

/--
[ons_internalPath_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean)
-/
@[path]
private lemma ons_internalPath_unique_eq
  {L : ℕ}
  {site : ZMod L × ZMod L}
  {a b : Fin 4}
  {p q : (ons_decGraph L).Walk (site, a) (site, b)}
-- given
  (hpint : ∀ d ∈ p.darts, ons_decInternalAdj d.fst d.snd)
  (hqint : ∀ d ∈ q.darts, ons_decInternalAdj d.fst d.snd)
  (hp : p.IsPath)
  (hq : q.IsPath) :
-- imply
  p = q := by
-- proof
  apply StatMech.Onsager.ons_internalPath_unique site a b p q hpint hqint hp hq

/--
[ons_decPortChainPath_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean)
-/
@[path]
private lemma ons_decPortChainPath_internal_eq
  {L : ℕ}
  [Fact (2 < L)]
  {site : ZMod L × ZMod L}
  {a b : Fin 4} :
-- imply
  ∀ d ∈ (ons_decPortChainPath L site a b).darts, ons_decInternalAdj d.fst d.snd := by
-- proof
  apply StatMech.Onsager.ons_decPortChainPath_internal L site a b

/--
[ons_internalPath_eq_decPortChainPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean)
-/
@[path]
private lemma ons_internalPath_eq_decPortChainPath_eq
  {L : ℕ}
  [Fact (2 < L)]
  {source target : ons_Dart L}
  {p : (ons_decGraph L).Walk (ons_dartRev L source) target}
-- given
  (hstep : target.1 = ons_dirStep L source.2 source.1)
  (hpint : ∀ d ∈ p.darts, ons_decInternalAdj d.fst d.snd)
  (hp : p.IsPath) :
-- imply
  p = (ons_decPortChainPath L target.1 (source.2 + 2) target.2).copy (by apply Prod.ext · exact hstep.trans (ons_dartRev_fst_eq_step L source).symm · simp [ons_dartRev]) rfl := by
-- proof
  apply StatMech.Onsager.ons_internalPath_eq_decPortChainPath L source target hstep p hpint hp

/--
[ons_decWalkOfKWChain_edges_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean)
-/
@[path]
private lemma ons_decWalkOfKWChain_edges_congr_eq
  {L : ℕ}
  {current : ons_Dart L}
  {tail tail' : List (ons_Dart L)}
-- given
  (htail : tail = tail')
  (hchain : List.IsChain (ons_decGeometricStep L) (current :: tail))
  (hchain' : List.IsChain (ons_decGeometricStep L) (current :: tail')) :
-- imply
  (ons_decWalkOfKWChain L current tail hchain).edges = (ons_decWalkOfKWChain L current tail' hchain').edges := by
-- proof
  apply StatMech.Onsager.ons_decWalkOfKWChain_edges_congr L current tail tail' htail hchain hchain'

/--
[ons_decWalkOfKWChain_edges_congr_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean)
-/
@[path]
private lemma ons_decWalkOfKWChain_edges_congr_root_eq
  {L : ℕ}
  {current current' : ons_Dart L}
  {tail tail' : List (ons_Dart L)}
-- given
  (hcurrent : current = current')
  (htail : tail = tail')
  (hchain : List.IsChain (ons_decGeometricStep L) (current :: tail))
  (hchain' : List.IsChain (ons_decGeometricStep L) (current' :: tail')) :
-- imply
  (ons_decWalkOfKWChain L current tail hchain).edges = (ons_decWalkOfKWChain L current' tail' hchain').edges := by
-- proof
  apply StatMech.Onsager.ons_decWalkOfKWChain_edges_congr_root L current current' tail tail' hcurrent htail hchain hchain'

/--
[ons_decWalkOfKWChain_rebuild](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean)
-/
@[path]
private lemma ons_decWalkOfKWChain_rebuild_eq
  {L : ℕ}
  [Fact (2 < L)]
  {current : ons_Dart L}
  {u finish : ons_Dart L}
  {r : (ons_decGraph L).Walk (ons_dartRev L current) u}
  {p : (ons_decGraph L).Walk u finish}
-- given
  (hrint : ∀ d ∈ r.darts, ons_decInternalAdj d.fst d.snd)
  (hrpath : r.IsPath)
  (hallpath : (r.append p).IsPath)
  (hchain : List.IsChain (ons_decGeometricStep L) (current :: (ons_decWalkExternalDarts p ++ [finish]))) :
-- imply
  ((ons_decExternalStepWalk L current).append (r.append p)).edges = (ons_decWalkOfKWChain L current (ons_decWalkExternalDarts p ++ [finish]) hchain).edges := by
-- proof
  apply StatMech.Onsager.ons_decWalkOfKWChain_rebuild L current r p hrint hrpath hallpath hchain

/--
[ons_decGeometricLoopStates_cycle_eq_externalDarts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean)
-/
@[path]
private lemma ons_decGeometricLoopStates_cycle_eq_externalDarts_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  List.ofFn (ons_decGeometricLoopStates (ons_decCycleDartLoop q)) = ons_decWalkExternalDarts q := by
-- proof
  apply StatMech.Onsager.ons_decGeometricLoopStates_cycle_eq_externalDarts q hq hsnd

/--
[ons_decLoopWalk_cycle_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean)
-/
@[path]
private lemma ons_decLoopWalk_cycle_edges_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  (ons_decLoopWalk L (ons_decCycleDartLoop q) (ons_decCycleDartLoop_valid q hq hsnd)).edges = q.edges := by
-- proof
  apply StatMech.Onsager.ons_decLoopWalk_cycle_edges q hq hsnd

/--
[ons_decCycleDartLoop_exponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean)
-/
@[path]
private lemma ons_decCycleDartLoop_exponent_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ons_decLoopExponent L (ons_decCycleDartLoop q) = ons_finsetExponent q.edges.toFinset := by
-- proof
  apply StatMech.Onsager.ons_decCycleDartLoop_exponent q hq hsnd

/--
[ons_decCycleDartLoop_scalar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean)
-/
@[path]
private lemma ons_decCycleDartLoop_scalar_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {a b : Fin 2}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (ons_decCycleDartLoop q) = -((ons_spinCharacter a b (ons_evenHomology L (ons_walkOriginalEdges q))) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decCycleDartLoop_scalar q hq hsnd a b

/--
[ons_decCycleDartLoop_scalar_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean)
-/
@[path]
private lemma ons_decCycleDartLoop_scalar_ne_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {a b : Fin 2}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (ons_decCycleDartLoop q) ≠ 0 := by
-- proof
  apply StatMech.Onsager.ons_decCycleDartLoop_scalar_ne_zero q hq hsnd a b

/--
[ons_decCycleDartLoop_mem_squarefreeLoopFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean)
-/
@[path]
private lemma ons_decCycleDartLoop_mem_squarefreeLoopFinset_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {a b : Fin 2}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ons_decCycleDartLoop q ∈ ons_decSquarefreeLoopFinset L a b q.edges.toFinset := by
-- proof
  apply StatMech.Onsager.ons_decCycleDartLoop_mem_squarefreeLoopFinset q hq hsnd a b

/--
[ons_decFormalLogCoeff_squarefree_of_mem_neZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean)
-/
@[path]
private lemma ons_decFormalLogCoeff_squarefree_of_mem_neZero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {S : Finset (ons_DecEdge L)}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hd : d ∈ ons_decSquarefreeLoopFinset L a b S) :
-- imply
  ons_decFormalLogCoeff L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (ons_finsetExponent S) = (ons_spinCharacter a b (ons_evenHomology L (ons_walkOriginalEdges (ons_decLoopWalk L d (ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d ((ons_mem_decSquarefreeLoopFinset L a b S d).mp hd).2)))) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decFormalLogCoeff_squarefree_of_mem_neZero L a b S d hd

/--
[ons_decFormalLogCoeff_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean)
-/
@[path]
private lemma ons_decFormalLogCoeff_cycle_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {a b : Fin 2}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ons_decFormalLogCoeff L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (ons_finsetExponent q.edges.toFinset) = (ons_spinCharacter a b (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decFormalLogCoeff_cycle q hq hsnd a b

/--
[ons_decFormalLogCoeff_unrooted_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean)
-/
@[path]
private lemma ons_decFormalLogCoeff_unrooted_cycle_eq
  {L : ℕ}
  [Fact (2 < L)]
  {root : ons_Dart L}
  {p : (ons_decGraph L).Walk root root}
  {a b : Fin 2}
-- given
  (hp : p.IsCycle) :
-- imply
  ons_decFormalLogCoeff L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (ons_finsetExponent p.edges.toFinset) = (ons_spinCharacter a b (ons_evenHomology L (ons_walkOriginalEdges p)) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decFormalLogCoeff_unrooted_cycle p hp a b


-- created on 2026-10-23
