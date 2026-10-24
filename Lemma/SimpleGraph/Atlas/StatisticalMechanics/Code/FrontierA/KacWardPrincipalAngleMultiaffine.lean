import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardPrincipalAngleMultiaffine
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[kwSpinorGraphLoopWeight_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalAngleMultiaffine.lean)
-/
@[path]
private lemma kwSpinorGraphLoopWeight_loopRev_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → Complex}
  {n : Nat}
  [NeZero n]
  {weight : Sym2 V → Complex}
  {loop : Fin n → G.Dart}
-- given
  (hphase : ∀ dart next, G.DartAdj dart next → dart.edge ≠ next.edge → phase next.symm dart.symm = (phase dart next)⁻¹)
  (hloopSq : ∀ {n : Nat} [NeZero n] (loop : Fin n → G.Dart), (∀ k : Fin n, G.DartAdj (loop k) (loop (k + 1)) ∧ (loop k).edge ≠ (loop (k + 1)).edge) → (∏ k, phase (loop k) (loop (k + 1))) ^ 2 = 1) :
-- imply
  ons_loopWeight (kwGraphTransition G weight phase) (ons_involutiveLoopRev SimpleGraph.Dart.symm loop) = ons_loopWeight (kwGraphTransition G weight phase) loop := by
-- proof
  apply StatMech.FrontierA.kwSpinorGraphLoopWeight_loopRev G phase hphase hloopSq weight loop

/--
[kwSpinorGraph_bothOrientation_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalAngleMultiaffine.lean)
-/
@[path]
private lemma kwSpinorGraph_bothOrientation_sum_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → Complex}
  {n : Nat}
  [NeZero n]
  {weight : Sym2 V → Complex}
  {selected : G.Dart}
-- given
  (hpathSq : ∀ {N : Nat} (path : Fin (N + 1) → G.Dart), path (Fin.last N) = (path 0).symm → (∀ j : Fin N, G.DartAdj (path j.castSucc) (path j.succ) ∧ (path j.castSucc).edge ≠ (path j.succ).edge) → (∏ j : Fin N, phase (path j.castSucc) (path j.succ)) ^ 2 = -1)
  (hphase : ∀ dart next, G.DartAdj dart next → dart.edge ≠ next.edge → phase next.symm dart.symm = (phase dart next)⁻¹) :
-- imply
  (∑ loop ∈ ons_loopSetBoth (n := n) selected selected.symm, ons_loopWeight (kwGraphTransition G weight phase) loop) = 0 := by
-- proof
  apply StatMech.FrontierA.kwSpinorGraph_bothOrientation_sum_zero G phase hpathSq hphase weight selected

/--
[kwSpinorGraph_oneOrientation_sum_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalAngleMultiaffine.lean)
-/
@[path]
private lemma kwSpinorGraph_oneOrientation_sum_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → Complex}
  {n : Nat}
  [NeZero n]
  {weight : Sym2 V → Complex}
  {selected : G.Dart}
-- given
  (hphase : ∀ dart next, G.DartAdj dart next → dart.edge ≠ next.edge → phase next.symm dart.symm = (phase dart next)⁻¹)
  (hloopSq : ∀ {n : Nat} [NeZero n] (loop : Fin n → G.Dart), (∀ k : Fin n, G.DartAdj (loop k) (loop (k + 1)) ∧ (loop k).edge ≠ (loop (k + 1)).edge) → (∏ k, phase (loop k) (loop (k + 1))) ^ 2 = 1) :
-- imply
  (∑ loop ∈ Finset.univ.filter (fun loop : Fin n → G.Dart ↦ (∃ i, loop i = selected) ∧ ¬∃ j, loop j = selected.symm), ons_loopWeight (kwGraphTransition G weight phase) loop) = ∑ loop ∈ Finset.univ.filter (fun loop : Fin n → G.Dart ↦ (∃ i, loop i = selected.symm) ∧ ¬∃ j, loop j = selected), ons_loopWeight (kwGraphTransition G weight phase) loop := by
-- proof
  apply StatMech.FrontierA.kwSpinorGraph_oneOrientation_sum_symm G phase hphase hloopSq weight selected

/--
[kwPrincipalAngleGraphLoopWeight_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalAngleMultiaffine.lean)
-/
@[path]
private lemma kwPrincipalAngleGraphLoopWeight_loopRev_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {angle : G.Dart → Real.Angle}
  {n : Nat}
  [NeZero n]
  {weight : Sym2 V → Complex}
  {loop : Fin n → G.Dart}
-- given
  (hangle : ∀ dart, angle dart.symm = angle dart + (Real.pi : Real.Angle))
  (hnonantipodal : ∀ dart next, G.DartAdj dart next → dart.edge ≠ next.edge → angle next - angle dart ≠ (Real.pi : Real.Angle)) :
-- imply
  ons_loopWeight (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle)) (ons_involutiveLoopRev SimpleGraph.Dart.symm loop) = ons_loopWeight (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle)) loop := by
-- proof
  apply StatMech.FrontierA.kwPrincipalAngleGraphLoopWeight_loopRev G angle hangle hnonantipodal weight loop

/--
[kwPrincipalAngleGraph_bothOrientation_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalAngleMultiaffine.lean)
-/
@[path]
private lemma kwPrincipalAngleGraph_bothOrientation_sum_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {angle : G.Dart → Real.Angle}
  {n : Nat}
  [NeZero n]
  {weight : Sym2 V → Complex}
  {selected : G.Dart}
-- given
  (hangle : ∀ dart, angle dart.symm = angle dart + (Real.pi : Real.Angle))
  (hnonantipodal : ∀ dart next, G.DartAdj dart next → dart.edge ≠ next.edge → angle next - angle dart ≠ (Real.pi : Real.Angle)) :
-- imply
  (∑ loop ∈ ons_loopSetBoth (n := n) selected selected.symm, ons_loopWeight (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle)) loop) = 0 := by
-- proof
  apply StatMech.FrontierA.kwPrincipalAngleGraph_bothOrientation_sum_zero G angle hangle hnonantipodal weight selected

/--
[kwPrincipalAngleGraph_oneOrientation_sum_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalAngleMultiaffine.lean)
-/
@[path]
private lemma kwPrincipalAngleGraph_oneOrientation_sum_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {angle : G.Dart → Real.Angle}
  {n : Nat}
  [NeZero n]
  {weight : Sym2 V → Complex}
  {selected : G.Dart}
-- given
  (hangle : ∀ dart, angle dart.symm = angle dart + (Real.pi : Real.Angle))
  (hnonantipodal : ∀ dart next, G.DartAdj dart next → dart.edge ≠ next.edge → angle next - angle dart ≠ (Real.pi : Real.Angle)) :
-- imply
  (∑ loop ∈ Finset.univ.filter (fun loop : Fin n → G.Dart ↦ (∃ i, loop i = selected) ∧ ¬∃ j, loop j = selected.symm), ons_loopWeight (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle)) loop) = ∑ loop ∈ Finset.univ.filter (fun loop : Fin n → G.Dart ↦ (∃ i, loop i = selected.symm) ∧ ¬∃ j, loop j = selected), ons_loopWeight (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle)) loop := by
-- proof
  apply StatMech.FrontierA.kwPrincipalAngleGraph_oneOrientation_sum_symm G angle hangle hnonantipodal weight selected

/--
[kwSpinorGraph_detWalkRoot_scaleEdge_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalAngleMultiaffine.lean)
-/
@[path]
private lemma kwSpinorGraph_detWalkRoot_scaleEdge_affine_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → Complex}
  {weight : Sym2 V → Complex}
  {selected : G.Dart}
  {t : Complex}
  {q : Real}
-- given
  (hpathSq : ∀ {N : Nat} (path : Fin (N + 1) → G.Dart), path (Fin.last N) = (path 0).symm → (∀ j : Fin N, G.DartAdj (path j.castSucc) (path j.succ) ∧ (path j.castSucc).edge ≠ (path j.succ).edge) → (∏ j : Fin N, phase (path j.castSucc) (path j.succ)) ^ 2 = -1)
  (hphase : ∀ dart next, G.DartAdj dart next → dart.edge ≠ next.edge → phase next.symm dart.symm = (phase dart next)⁻¹)
  (hloopSq : ∀ {n : Nat} [NeZero n] (loop : Fin n → G.Dart), (∀ k : Fin n, G.DartAdj (loop k) (loop (k + 1)) ∧ (loop k).edge ≠ (loop (k + 1)).edge) → (∏ k, phase (loop k) (loop (k + 1))) ^ 2 = 1)
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖ons_scaleColumns ({selected, selected.symm} : Finset G.Dart) t (kwGraphTransition G weight phase) dart next‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card G.Dart : Real) ^ 2)⁻¹)
  (hcard : (Fintype.card G.Dart : Real) * q < 1) :
-- imply
  ons_detWalkRoot (kwGraphTransition G (kwScaleGraphEdgeWeight weight selected.edge t) phase) = ons_detWalkRoot (ons_maskMatrix ({selected, selected.symm} : Finset G.Dart) (kwGraphTransition G weight phase)) * (1 - t * ∑' path, ons_firstReturnWeight (kwGraphTransition G weight phase) selected selected.symm path) := by
-- proof
  apply StatMech.FrontierA.kwSpinorGraph_detWalkRoot_scaleEdge_affine G phase hpathSq hphase hloopSq weight selected t q hq hentry hsmall hcard

/--
[kw_spinorGraph_formalRoot_coeff_eq_zero_of_repeated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalAngleMultiaffine.lean)
-/
@[path]
private lemma kw_spinorGraph_formalRoot_coeff_eq_zero_of_repeated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → Complex}
  {selected : G.Dart}
  {m : Sym2 V →₀ Nat}
-- given
  (hpathSq : ∀ {N : Nat} (path : Fin (N + 1) → G.Dart), path (Fin.last N) = (path 0).symm → (∀ j : Fin N, G.DartAdj (path j.castSucc) (path j.succ) ∧ (path j.castSucc).edge ≠ (path j.succ).edge) → (∏ j : Fin N, phase (path j.castSucc) (path j.succ)) ^ 2 = -1)
  (hphase : ∀ dart next, G.DartAdj dart next → dart.edge ≠ next.edge → phase next.symm dart.symm = (phase dart next)⁻¹)
  (hloopSq : ∀ {n : Nat} [NeZero n] (loop : Fin n → G.Dart), (∀ k : Fin n, G.DartAdj (loop k) (loop (k + 1)) ∧ (loop k).edge ≠ (loop (k + 1)).edge) → (∏ k, phase (loop k) (loop (k + 1))) ^ 2 = 1)
  (hrepeated : 2 ≤ m selected.edge) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_spinorGraph_formalRoot_coeff_eq_zero_of_repeated G phase hpathSq hphase hloopSq selected m hrepeated

/--
[kwPrincipalAngleGraph_detWalkRoot_scaleEdge_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalAngleMultiaffine.lean)
-/
@[path]
private lemma kwPrincipalAngleGraph_detWalkRoot_scaleEdge_affine_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {angle : G.Dart → Real.Angle}
  {weight : Sym2 V → Complex}
  {selected : G.Dart}
  {t : Complex}
  {q : Real}
-- given
  (hangle : ∀ dart, angle dart.symm = angle dart + (Real.pi : Real.Angle))
  (hnonantipodal : ∀ dart next, G.DartAdj dart next → dart.edge ≠ next.edge → angle next - angle dart ≠ (Real.pi : Real.Angle))
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖ons_scaleColumns ({selected, selected.symm} : Finset G.Dart) t (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle)) dart next‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card G.Dart : Real) ^ 2)⁻¹)
  (hcard : (Fintype.card G.Dart : Real) * q < 1) :
-- imply
  ons_detWalkRoot (kwGraphTransition G (kwScaleGraphEdgeWeight weight selected.edge t) (kwPrincipalHalfAnglePhase angle)) = ons_detWalkRoot (ons_maskMatrix ({selected, selected.symm} : Finset G.Dart) (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle))) * (1 - t * ∑' path, ons_firstReturnWeight (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle)) selected selected.symm path) := by
-- proof
  apply StatMech.FrontierA.kwPrincipalAngleGraph_detWalkRoot_scaleEdge_affine G angle hangle hnonantipodal weight selected t q hq hentry hsmall hcard

/--
[kw_principalAngleGraph_formalRoot_coeff_eq_zero_of_repeated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalAngleMultiaffine.lean)
-/
@[path]
private lemma kw_principalAngleGraph_formalRoot_coeff_eq_zero_of_repeated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {angle : G.Dart → Real.Angle}
  {selected : G.Dart}
  {m : Sym2 V →₀ Nat}
-- given
  (hangle : ∀ dart, angle dart.symm = angle dart + (Real.pi : Real.Angle))
  (hnonantipodal : ∀ dart next, G.DartAdj dart next → dart.edge ≠ next.edge → angle next - angle dart ≠ (Real.pi : Real.Angle))
  (hrepeated : 2 ≤ m selected.edge) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot G (kwPrincipalHalfAnglePhase angle)) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_principalAngleGraph_formalRoot_coeff_eq_zero_of_repeated G angle hangle hnonantipodal selected m hrepeated


-- created on 2026-10-23
