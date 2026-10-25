import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardReversibleCycleCoefficient.Part2
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[kwGraphLoop_nonbacktracking_of_scalar_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardReversibleCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphLoop_nonbacktracking_of_scalar_ne_zero_eq
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
  kwGraphLoopNonbacktracking G loop := by
-- proof
  apply StatMech.FrontierA.kwGraphLoop_nonbacktracking_of_scalar_ne_zero G phase loop hscalar

/--
[kwGraphLoopOrientation_mem_of_reversalInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardReversibleCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphLoopOrientation_mem_of_reversalInvariant_eq
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
  {orientation : Fin n ⊕ Fin n}
-- given
  (hrev : KWGraphLoopReversalInvariant G phase)
  (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S) :
-- imply
  kwGraphLoopOrientation loop orientation ∈ kwGraphSquarefreeLoopFinset G phase S := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopOrientation_mem_of_reversalInvariant G phase hrev S hloop orientation

/--
[kwGraphSquarefreeLoopFinset_card_of_reversalInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardReversibleCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphSquarefreeLoopFinset_card_of_reversalInvariant_eq
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
  (hrev : KWGraphLoopReversalInvariant G phase)
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S) :
-- imply
  (kwGraphSquarefreeLoopFinset (n := n) G phase S).card = 2 * n := by
-- proof
  apply StatMech.FrontierA.kwGraphSquarefreeLoopFinset_card_of_reversalInvariant G phase hrev hdeg S hloop

/--
[kwGraphSquarefreeLoop_scalar_eq_of_reversalInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardReversibleCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphSquarefreeLoop_scalar_eq_of_reversalInvariant_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {n : ℕ}
  [NeZero n]
  {S : Finset (Sym2 V)}
  {d e : Fin n → G.Dart}
-- given
  (hrev : KWGraphLoopReversalInvariant G phase)
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hd : d ∈ kwGraphSquarefreeLoopFinset G phase S)
  (he : e ∈ kwGraphSquarefreeLoopFinset G phase S) :
-- imply
  kwGraphLoopScalar G phase e = kwGraphLoopScalar G phase d := by
-- proof
  apply StatMech.FrontierA.kwGraphSquarefreeLoop_scalar_eq_of_reversalInvariant G phase hrev hdeg S hd he

/--
[kwGraphSquarefreeLoop_bucket_sum_of_reversalInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardReversibleCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphSquarefreeLoop_bucket_sum_of_reversalInvariant_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {n : ℕ}
  [NeZero n]
  {S : Finset (Sym2 V)}
  {d : Fin n → G.Dart}
-- given
  (hrev : KWGraphLoopReversalInvariant G phase)
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hd : d ∈ kwGraphSquarefreeLoopFinset G phase S) :
-- imply
  (∑ e : Fin n → G.Dart, if kwGraphLoopExponent G e = ons_finsetExponent S then kwGraphLoopScalar G phase e else 0) = (2 * n : ℂ) * kwGraphLoopScalar G phase d := by
-- proof
  apply StatMech.FrontierA.kwGraphSquarefreeLoop_bucket_sum_of_reversalInvariant G phase hrev hdeg S hd

/--
[kwGraphFormalLogCoeff_squarefree_of_mem_reversalInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardReversibleCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphFormalLogCoeff_squarefree_of_mem_reversalInvariant_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {S : Finset (Sym2 V)}
  {r : ℕ}
  {d : Fin (r + 1) → G.Dart}
-- given
  (hrev : KWGraphLoopReversalInvariant G phase)
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hd : d ∈ kwGraphSquarefreeLoopFinset G phase S) :
-- imply
  kwGraphFormalLogCoeff G phase (ons_finsetExponent S) = -kwGraphLoopScalar G phase d := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLogCoeff_squarefree_of_mem_reversalInvariant G phase hrev hdeg S r d hd

/--
[kwGraphFormalLogCoeff_squarefree_eq_one_of_reversalInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardReversibleCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphFormalLogCoeff_squarefree_eq_one_of_reversalInvariant_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {S : Finset (Sym2 V)}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → G.Dart}
-- given
  (hrev : KWGraphLoopReversalInvariant G phase)
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hd : d ∈ kwGraphSquarefreeLoopFinset G phase S)
  (hscalar : kwGraphLoopScalar G phase d = -1) :
-- imply
  kwGraphFormalLogCoeff G phase (ons_finsetExponent S) = 1 := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLogCoeff_squarefree_eq_one_of_reversalInvariant G phase hrev hdeg S d hd hscalar

/--
[kwGraphFormalLogCoeff_cycle_of_reversalInvariant_phaseProduct_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardReversibleCycleCoefficient.lean)
-/
@[path]
private lemma kwGraphFormalLogCoeff_cycle_of_reversalInvariant_phaseProduct_neg_one_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {root : V}
  {p : G.Walk root root}
-- given
  (hrev : KWGraphLoopReversalInvariant G phase)
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hp : p.IsCycle)
  (hphase : letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ kwLoopPhaseProduct phase (kwGraphCycleDartLoop p) = -1) :
-- imply
  kwGraphFormalLogCoeff G phase (ons_finsetExponent p.edges.toFinset) = 1 := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLogCoeff_cycle_of_reversalInvariant_phaseProduct_neg_one G phase hrev hdeg p hp hphase


-- created on 2026-10-23
