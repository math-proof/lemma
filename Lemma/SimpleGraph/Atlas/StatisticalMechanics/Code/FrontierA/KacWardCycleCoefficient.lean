import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardCycleCoefficient
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[kwGraph_mem_squarefreeLoopFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraph_mem_squarefreeLoopFinset_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {n : ℕ}
  [NeZero n]
  {S : Finset (Sym2 V)}
  {loop : Fin n → G.Dart} :
-- imply
  loop ∈ kwGraphSquarefreeLoopFinset G phase S ↔ kwGraphLoopExponent G loop = ons_finsetExponent S ∧ kwGraphLoopScalar G phase loop ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwGraph_mem_squarefreeLoopFinset G phase S loop

/--
[kwGraphLoopWalk_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphLoopWalk_snd_eq
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
  (kwGraphLoopWalk G loop hvalid).snd = (loop 0).snd := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopWalk_snd G loop hvalid

/--
[kwGraph_squarefreeLoop_eval_zero_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraph_squarefreeLoop_eval_zero_injective_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {n : ℕ}
  [NeZero n]
  {S : Finset (Sym2 V)}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3) :
-- imply
  Set.InjOn (fun loop : Fin n → G.Dart ↦ loop 0) (kwGraphSquarefreeLoopFinset (n := n) G phase S : Set (Fin n → G.Dart)) := by
-- proof
  apply StatMech.FrontierA.kwGraph_squarefreeLoop_eval_zero_injective G phase hdeg S

/--
[kwGraphLoopExponent_rotate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphLoopExponent_rotate_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart}
  {r : Fin n} :
-- imply
  kwGraphLoopExponent G (ons_rotate r loop) = kwGraphLoopExponent G loop := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopExponent_rotate G loop r

/--
[kwGraphLoopScalar_rotate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphLoopScalar_rotate_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart}
  {r : Fin n} :
-- imply
  kwGraphLoopScalar G phase (ons_rotate r loop) = kwGraphLoopScalar G phase loop := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopScalar_rotate G phase loop r

/--
[kwGraphLoopRev_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphLoopRev_apply_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart}
  {k : Fin n} :
-- imply
  kwGraphLoopRev loop k = (loop (-k)).symm := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopRev_apply loop k

/--
[kwGraphLoopExponent_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphLoopExponent_loopRev_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart} :
-- imply
  kwGraphLoopExponent G (kwGraphLoopRev loop) = kwGraphLoopExponent G loop := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopExponent_loopRev G loop

/--
[kwGraphLoopScalar_loopRev_straightLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphLoopScalar_loopRev_straightLine_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart} :
-- imply
  kwGraphLoopScalar G embedding.turnPhase (kwGraphLoopRev loop) = kwGraphLoopScalar G embedding.turnPhase loop := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopScalar_loopRev_straightLine G embedding loop

/--
[kwGraphLoopRootFinset_card_of_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphLoopRootFinset_card_of_squarefree_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {n : ℕ}
  [NeZero n]
  {S : Finset (Sym2 V)}
  {loop : Fin n → G.Dart}
-- given
  (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S) :
-- imply
  (kwGraphLoopRootFinset loop).card = 2 * n := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopRootFinset_card_of_squarefree G phase S hloop

/--
[kwGraph_squarefreeLoop_root_edge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraph_squarefreeLoop_root_edge_mem_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {n : ℕ}
  [NeZero n]
  {S : Finset (Sym2 V)}
  {loop : Fin n → G.Dart}
-- given
  (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S) :
-- imply
  (loop 0).edge ∈ S := by
-- proof
  apply StatMech.FrontierA.kwGraph_squarefreeLoop_root_edge_mem G phase S hloop

/--
[kwGraph_root_mem_loopRootFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraph_root_mem_loopRootFinset_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {n : ℕ}
  [NeZero n]
  {S : Finset (Sym2 V)}
  {loop : Fin n → G.Dart}
  {root : G.Dart}
-- given
  (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S)
  (hroot : root.edge ∈ S) :
-- imply
  root ∈ kwGraphLoopRootFinset loop := by
-- proof
  apply StatMech.FrontierA.kwGraph_root_mem_loopRootFinset G phase S hloop root hroot

/--
[kwGraphLoopOrientation_mem_straightLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphLoopOrientation_mem_straightLine_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : ℕ}
  [NeZero n]
  {S : Finset (Sym2 V)}
  {loop : Fin n → G.Dart}
  {orientation : Fin n ⊕ Fin n}
-- given
  (hloop : loop ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S) :
-- imply
  kwGraphLoopOrientation loop orientation ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopOrientation_mem_straightLine G embedding S hloop orientation

/--
[kwGraphLoopOrientation_injective_of_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphLoopOrientation_injective_of_squarefree_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {n : ℕ}
  [NeZero n]
  {S : Finset (Sym2 V)}
  {loop : Fin n → G.Dart}
-- given
  (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S) :
-- imply
  Function.Injective (kwGraphLoopOrientation loop) := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopOrientation_injective_of_squarefree G phase S hloop

/--
[kwGraphSquarefreeLoopFinset_card_straightLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphSquarefreeLoopFinset_card_straightLine_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : ℕ}
  [NeZero n]
  {S : Finset (Sym2 V)}
  {loop : Fin n → G.Dart}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hloop : loop ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S) :
-- imply
  (kwGraphSquarefreeLoopFinset (n := n) G embedding.turnPhase S).card = 2 * n := by
-- proof
  apply StatMech.FrontierA.kwGraphSquarefreeLoopFinset_card_straightLine G embedding hdeg S hloop

/--
[kwGraphSquarefreeLoop_scalar_eq_straightLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphSquarefreeLoop_scalar_eq_straightLine_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : ℕ}
  [NeZero n]
  {S : Finset (Sym2 V)}
  {d e : Fin n → G.Dart}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hd : d ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S)
  (he : e ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S) :
-- imply
  kwGraphLoopScalar G embedding.turnPhase e = kwGraphLoopScalar G embedding.turnPhase d := by
-- proof
  apply StatMech.FrontierA.kwGraphSquarefreeLoop_scalar_eq_straightLine G embedding hdeg S hd he

/--
[kwGraphSquarefreeLoop_bucket_sum_straightLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphSquarefreeLoop_bucket_sum_straightLine_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : ℕ}
  [NeZero n]
  {S : Finset (Sym2 V)}
  {d : Fin n → G.Dart}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hd : d ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S) :
-- imply
  (∑ e : Fin n → G.Dart, if kwGraphLoopExponent G e = ons_finsetExponent S then kwGraphLoopScalar G embedding.turnPhase e else 0) = (2 * n : ℂ) * kwGraphLoopScalar G embedding.turnPhase d := by
-- proof
  apply StatMech.FrontierA.kwGraphSquarefreeLoop_bucket_sum_straightLine G embedding hdeg S hd

/--
[kwGraphFormalLogCoeff_squarefree_of_mem_straightLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphFormalLogCoeff_squarefree_of_mem_straightLine_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {S : Finset (Sym2 V)}
  {r : ℕ}
  {d : Fin (r + 1) → G.Dart}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hd : d ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S) :
-- imply
  kwGraphFormalLogCoeff G embedding.turnPhase (ons_finsetExponent S) = -kwGraphLoopScalar G embedding.turnPhase d := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLogCoeff_squarefree_of_mem_straightLine G embedding hdeg S r d hd

/--
[kwGraphFormalLogCoeff_squarefree_eq_one_of_scalar_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphFormalLogCoeff_squarefree_eq_one_of_scalar_neg_one_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {S : Finset (Sym2 V)}
  {r : ℕ}
  {d : Fin (r + 1) → G.Dart}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hd : d ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S)
  (hscalar : kwGraphLoopScalar G embedding.turnPhase d = -1) :
-- imply
  kwGraphFormalLogCoeff G embedding.turnPhase (ons_finsetExponent S) = 1 := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLogCoeff_squarefree_eq_one_of_scalar_neg_one G embedding hdeg S r d hd hscalar

/--
[kwGraphFormalLogCoeff_squarefree_eq_one_of_scalar_neg_one'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphFormalLogCoeff_squarefree_eq_one_of_scalar_neg_one'_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {S : Finset (Sym2 V)}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → G.Dart}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hd : d ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S)
  (hscalar : kwGraphLoopScalar G embedding.turnPhase d = -1) :
-- imply
  kwGraphFormalLogCoeff G embedding.turnPhase (ons_finsetExponent S) = 1 := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLogCoeff_squarefree_eq_one_of_scalar_neg_one' G embedding hdeg S d hd hscalar

/--
[kwGraphCycleDartLoop_ofFn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphCycleDartLoop_ofFn_eq
  {V : Type u}
  {G : SimpleGraph V}
  {root : V}
  {p : G.Walk root root} :
-- imply
  List.ofFn (kwGraphCycleDartLoop p) = p.darts := by
-- proof
  apply StatMech.FrontierA.kwGraphCycleDartLoop_ofFn p

/--
[kwGraphCycleDartLoop_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphCycleDartLoop_valid_eq
  {V : Type u}
  {G : SimpleGraph V}
  {root : V}
  {p : G.Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ ∀ k, G.DartAdj (kwGraphCycleDartLoop p k) (kwGraphCycleDartLoop p (k + 1)) := by
-- proof
  apply StatMech.FrontierA.kwGraphCycleDartLoop_valid p hp

/--
[kwGraphCycleDartLoop_exponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphCycleDartLoop_exponent_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {root : V}
  {p : G.Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ kwGraphLoopExponent G (kwGraphCycleDartLoop p) = ons_finsetExponent p.edges.toFinset := by
-- proof
  apply StatMech.FrontierA.kwGraphCycleDartLoop_exponent G p hp

/--
[kwGraphCycleDartLoop_nonbacktracking](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphCycleDartLoop_nonbacktracking_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {root : V}
  {p : G.Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ kwGraphLoopNonbacktracking G (kwGraphCycleDartLoop p) := by
-- proof
  apply StatMech.FrontierA.kwGraphCycleDartLoop_nonbacktracking G p hp

/--
[kwGraphCycleDartLoop_scalar_eq_phaseProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphCycleDartLoop_scalar_eq_phaseProduct_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {root : V}
  {p : G.Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ kwGraphLoopScalar G phase (kwGraphCycleDartLoop p) = kwLoopPhaseProduct phase (kwGraphCycleDartLoop p) := by
-- proof
  apply StatMech.FrontierA.kwGraphCycleDartLoop_scalar_eq_phaseProduct G phase p hp

/--
[kwGraphFormalLogCoeff_cycle_of_phaseProduct_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphFormalLogCoeff_cycle_of_phaseProduct_neg_one_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hp : p.IsCycle)
  (hphase : letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ kwLoopPhaseProduct embedding.turnPhase (kwGraphCycleDartLoop p) = -1) :
-- imply
  kwGraphFormalLogCoeff G embedding.turnPhase (ons_finsetExponent p.edges.toFinset) = 1 := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLogCoeff_cycle_of_phaseProduct_neg_one G embedding hdeg p hp hphase


-- created on 2026-10-23
