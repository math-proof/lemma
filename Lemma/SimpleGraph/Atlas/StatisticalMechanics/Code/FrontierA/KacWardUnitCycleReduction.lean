import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnitCycleReduction
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[kwGraphLoopWalk_darts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnitCycleReduction.lean)
-/
@[path]
private lemma kwGraphLoopWalk_darts_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart}
-- given
  (hvalid : ∀ k, G.DartAdj (loop k) (loop (k + 1))) :
-- imply
  (kwGraphLoopWalk G loop hvalid).darts = List.ofFn loop := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopWalk_darts G loop hvalid

/--
[kwGraphLoopWalk_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnitCycleReduction.lean)
-/
@[path]
private lemma kwGraphLoopWalk_edges_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart}
-- given
  (hvalid : ∀ k, G.DartAdj (loop k) (loop (k + 1))) :
-- imply
  (kwGraphLoopWalk G loop hvalid).edges = (List.ofFn loop).map SimpleGraph.Dart.edge := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopWalk_edges G loop hvalid

/--
[kwGraphLoopWalk_edgeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnitCycleReduction.lean)
-/
@[path]
private lemma kwGraphLoopWalk_edgeCount_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart}
-- given
  (hvalid : ∀ k, G.DartAdj (loop k) (loop (k + 1))) :
-- imply
  Multiset.toFinsupp ((kwGraphLoopWalk G loop hvalid).edges : Multiset (Sym2 V)) = kwGraphLoopExponent G loop := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopWalk_edgeCount G loop hvalid

/--
[kwGraphLoopWalk_isTrail_and_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnitCycleReduction.lean)
-/
@[path]
private lemma kwGraphLoopWalk_isTrail_and_edges_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart}
  {S : Finset (Sym2 V)}
-- given
  (hvalid : ∀ k, G.DartAdj (loop k) (loop (k + 1)))
  (hexponent : kwGraphLoopExponent G loop = ons_finsetExponent S) :
-- imply
  (kwGraphLoopWalk G loop hvalid).IsTrail ∧ (kwGraphLoopWalk G loop hvalid).edges.toFinset = S := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopWalk_isTrail_and_edges G loop hvalid S hexponent

/--
[kwGraphLoop_valid_of_scalar_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnitCycleReduction.lean)
-/
@[path]
private lemma kwGraphLoop_valid_of_scalar_ne_zero_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart}
-- given
  (hscalar : kwGraphLoopScalar G phase loop ≠ 0) :
-- imply
  ∀ k, G.DartAdj (loop k) (loop (k + 1)) := by
-- proof
  apply StatMech.FrontierA.kwGraphLoop_valid_of_scalar_ne_zero G phase loop hscalar

/--
[kw_closedTrail_isCycle_of_degree_le_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnitCycleReduction.lean)
-/
@[path]
private lemma kw_closedTrail_isCycle_of_degree_le_three_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {root : V}
  {p : G.Walk root root}
-- given
  (hp : p.IsTrail)
  (hne : p ≠ .nil)
  (hdeg : ∀ vertex, G.degree vertex ≤ 3) :
-- imply
  p.IsCycle := by
-- proof
  apply StatMech.FrontierA.kw_closedTrail_isCycle_of_degree_le_three G p hp hne hdeg

/--
[kwGraphFormalLogCoeff_squarefree_cycle_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnitCycleReduction.lean)
-/
@[path]
private lemma kwGraphFormalLogCoeff_squarefree_cycle_of_ne_zero_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {S : Finset (Sym2 V)}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hne : kwGraphFormalLogCoeff G phase (ons_finsetExponent S) ≠ 0) :
-- imply
  ∃ (root : V) (p : G.Walk root root), p.IsCycle ∧ p.edges.toFinset = S := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLogCoeff_squarefree_cycle_of_ne_zero G phase hdeg S hne

/--
[kwGraphUnitCycleLog_iff_cycleCoeff_of_degree_le_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnitCycleReduction.lean)
-/
@[path]
private lemma kwGraphUnitCycleLog_iff_cycleCoeff_of_degree_le_three_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3) :
-- imply
  KWGraphUnitCycleLog G phase ↔ ∀ {root : V} (p : G.Walk root root), p.IsCycle → kwGraphFormalLogCoeff G phase (ons_finsetExponent p.edges.toFinset) = 1 := by
-- proof
  apply StatMech.FrontierA.kwGraphUnitCycleLog_iff_cycleCoeff_of_degree_le_three G phase hdeg

/--
[kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_cycleCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnitCycleReduction.lean)
-/
@[path]
private lemma kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_cycleCoeff_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hcycle : ∀ {root : V} (p : G.Walk root root), p.IsCycle → kwGraphFormalLogCoeff G embedding.turnPhase (ons_finsetExponent p.edges.toFinset) = 1) :
-- imply
  kwGraphFormalRoot G embedding.turnPhase = kwGraphFormalEvenPolynomial G := by
-- proof
  apply StatMech.FrontierA.kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_cycleCoeff G embedding hdeg hcycle

/--
[kw_straightLineGraph_detWalkRoot_eq_evenPolynomial_of_cycleCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnitCycleReduction.lean)
-/
@[path]
private lemma kw_straightLineGraph_detWalkRoot_eq_evenPolynomial_of_cycleCoeff_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {q : ℝ}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hcycle : ∀ {root : V} (p : G.Walk root root), p.IsCycle → kwGraphFormalLogCoeff G embedding.turnPhase (ons_finsetExponent p.edges.toFinset) = 1)
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖kwGraphTransition G weight embedding.turnPhase dart next‖ ≤ q)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  StatMech.Onsager.ons_detWalkRoot (kwGraphTransition G weight embedding.turnPhase) = kwEvenPolynomial G weight := by
-- proof
  apply StatMech.FrontierA.kw_straightLineGraph_detWalkRoot_eq_evenPolynomial_of_cycleCoeff G embedding hdeg hcycle weight q hq hentry hcard

/--
[kacWard_straightLine_trivalent_of_cycleCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnitCycleReduction.lean)
-/
@[path]
private lemma kacWard_straightLine_trivalent_of_cycleCoeff_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {q : ℝ}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hcycle : ∀ {root : V} (p : G.Walk root root), p.IsCycle → kwGraphFormalLogCoeff G embedding.turnPhase (ons_finsetExponent p.edges.toFinset) = 1)
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖kwGraphTransition G weight embedding.turnPhase dart next‖ ≤ q)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  (1 - kwGraphTransition G weight embedding.turnPhase).det = (kwEvenPolynomial G weight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_straightLine_trivalent_of_cycleCoeff G embedding hdeg hcycle weight q hq hentry hcard


-- created on 2026-10-23
