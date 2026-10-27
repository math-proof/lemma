import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPrincipalCancellation
open StatMech StatMech.FrontierA


/--
[kw_phaseProduct_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalCancellation.lean)
-/
@[path]
private lemma kw_phaseProduct_surgery_sign_eq
  [Fintype Dart]
  [DecidableEq Dart]
  {n : ℕ}
  [NeZero n]
  {reverse : Dart → Dart}
  {phase : Dart → Dart → ℂ}
  {selected : Dart}
  {loop : Fin n → Dart}
-- given
  (hreverse : Function.Involutive reverse)
  (hreverse_ne : ∀ dart, reverse dart ≠ dart)
  (valid : Dart → Dart → Prop)
  (hpathSq : ∀ {N : ℕ} (path : Fin (N + 1) → Dart), path (Fin.last N) = reverse (path 0) → (∀ j : Fin N, valid (path j.castSucc) (path j.succ)) → (∏ j : Fin N, phase (path j.castSucc) (path j.succ)) ^ 2 = -1)
  (hboth : (∃ i, loop i = selected) ∧ ∃ j, loop j = reverse selected)
  (hvalid : ∀ k : Fin n, valid (loop k) (loop (k + 1)))
  (hphase : ∀ k : Fin n, phase (reverse (loop (k + 1))) (reverse (loop k)) = (phase (loop k) (loop (k + 1)))⁻¹) :
-- imply
  (∏ k, phase (StatMech.Onsager.ons_surgery selected reverse loop k) (StatMech.Onsager.ons_surgery selected reverse loop (k + 1))) = -∏ k, phase (loop k) (loop (k + 1)) := by
-- proof
  apply StatMech.FrontierA.kw_phaseProduct_surgery_sign reverse hreverse hreverse_ne phase valid hpathSq selected loop hboth hvalid hphase

/--
[kw_reversibleFactorProduct_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalCancellation.lean)
-/
@[path]
private lemma kw_reversibleFactorProduct_surgery_eq
  [Fintype Dart]
  [DecidableEq Dart]
  {n : ℕ}
  [NeZero n]
  {reverse : Dart → Dart}
  {factor : Dart → Dart → ℂ}
  {selected : Dart}
  {loop : Fin n → Dart}
-- given
  (hreverse : Function.Involutive reverse)
  (hreverse_ne : ∀ dart, reverse dart ≠ dart)
  (hfactor : ∀ x y, factor (reverse y) (reverse x) = factor x y)
  (hboth : (∃ i, loop i = selected) ∧ ∃ j, loop j = reverse selected) :
-- imply
  (∏ k, factor (StatMech.Onsager.ons_surgery selected reverse loop k) (StatMech.Onsager.ons_surgery selected reverse loop (k + 1))) = ∏ k, factor (loop k) (loop (k + 1)) := by
-- proof
  apply StatMech.FrontierA.kw_reversibleFactorProduct_surgery reverse hreverse hreverse_ne factor hfactor selected loop hboth

/--
[kwPrincipalHalfAnglePhase_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalCancellation.lean)
-/
@[path]
private lemma kwPrincipalHalfAnglePhase_reverse_eq
  {reverse : Dart → Dart}
  {angle : Dart → Real.Angle}
  {x y : Dart}
-- given
  (hangle : ∀ dart, angle (reverse dart) = angle dart + (Real.pi : Real.Angle))
  (hnonantipodal : angle y - angle x ≠ (Real.pi : Real.Angle)) :
-- imply
  kwPrincipalHalfAnglePhase angle (reverse y) (reverse x) = (kwPrincipalHalfAnglePhase angle x y)⁻¹ := by
-- proof
  apply StatMech.FrontierA.kwPrincipalHalfAnglePhase_reverse reverse angle hangle hnonantipodal

/--
[kwPrincipalHalfAnglePath_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalCancellation.lean)
-/
@[path]
private lemma kwPrincipalHalfAnglePath_sq_eq
  {reverse : Dart → Dart}
  {angle : Dart → Real.Angle}
  {N : ℕ}
  {path : Fin (N + 1) → Dart}
-- given
  (hangle : ∀ dart, angle (reverse dart) = angle dart + (Real.pi : Real.Angle))
  (hend : path (Fin.last N) = reverse (path 0)) :
-- imply
  (∏ j : Fin N, kwPrincipalHalfAnglePhase angle (path j.castSucc) (path j.succ)) ^ 2 = -1 := by
-- proof
  apply StatMech.FrontierA.kwPrincipalHalfAnglePath_sq reverse angle hangle path hend

/--
[kwPrincipalHalfAnglePhase_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalCancellation.lean)
-/
@[path]
private lemma kwPrincipalHalfAnglePhase_surgery_sign_eq
  [Fintype Dart]
  [DecidableEq Dart]
  {n : ℕ}
  [NeZero n]
  {reverse : Dart → Dart}
  {angle : Dart → Real.Angle}
  {selected : Dart}
  {loop : Fin n → Dart}
-- given
  (hreverse : Function.Involutive reverse)
  (hreverse_ne : ∀ dart, reverse dart ≠ dart)
  (hangle : ∀ dart, angle (reverse dart) = angle dart + (Real.pi : Real.Angle))
  (hboth : (∃ i, loop i = selected) ∧ ∃ j, loop j = reverse selected)
  (hnonantipodal : ∀ k : Fin n, angle (loop (k + 1)) - angle (loop k) ≠ (Real.pi : Real.Angle)) :
-- imply
  (∏ k, kwPrincipalHalfAnglePhase angle (StatMech.Onsager.ons_surgery selected reverse loop k) (StatMech.Onsager.ons_surgery selected reverse loop (k + 1))) = -∏ k, kwPrincipalHalfAnglePhase angle (loop k) (loop (k + 1)) := by
-- proof
  apply StatMech.FrontierA.kwPrincipalHalfAnglePhase_surgery_sign reverse hreverse hreverse_ne angle hangle selected loop hboth hnonantipodal

/--
[kwLoopPhaseProduct_involutiveLoopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalCancellation.lean)
-/
@[path]
private lemma kwLoopPhaseProduct_involutiveLoopRev_eq
  {n : ℕ}
  [NeZero n]
  {reverse : Dart → Dart}
  {phase : Dart → Dart → ℂ}
  {loop : Fin n → Dart}
-- given
  (hphase : ∀ k : Fin n, phase (reverse (loop (k + 1))) (reverse (loop k)) = (phase (loop k) (loop (k + 1)))⁻¹)
  (hPsq : kwLoopPhaseProduct phase loop ^ 2 = 1) :
-- imply
  kwLoopPhaseProduct phase (StatMech.Onsager.ons_involutiveLoopRev reverse loop) = kwLoopPhaseProduct phase loop := by
-- proof
  apply StatMech.FrontierA.kwLoopPhaseProduct_involutiveLoopRev reverse phase loop hphase hPsq

/--
[kwLoopPhaseProduct_principal_involutiveLoopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalCancellation.lean)
-/
@[path]
private lemma kwLoopPhaseProduct_principal_involutiveLoopRev_eq
  {n : ℕ}
  [NeZero n]
  {reverse : Dart → Dart}
  {angle : Dart → Real.Angle}
  {loop : Fin n → Dart}
-- given
  (hangle : ∀ dart, angle (reverse dart) = angle dart + (Real.pi : Real.Angle))
  (hnonantipodal : ∀ k : Fin n, angle (loop (k + 1)) - angle (loop k) ≠ (Real.pi : Real.Angle)) :
-- imply
  kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle) (StatMech.Onsager.ons_involutiveLoopRev reverse loop) = kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle) loop := by
-- proof
  apply StatMech.FrontierA.kwLoopPhaseProduct_principal_involutiveLoopRev reverse angle hangle loop hnonantipodal

/--
[kwGraphLoopScalar_eq_nonbacktracking_mul_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalCancellation.lean)
-/
@[path]
private lemma kwGraphLoopScalar_eq_nonbacktracking_mul_phase_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart} :
-- imply
  kwGraphLoopScalar G phase loop = (∏ k, kwGraphNonbacktrackingFactor G (loop k) (loop (k + 1))) * ∏ k, phase (loop k) (loop (k + 1)) := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopScalar_eq_nonbacktracking_mul_phase G phase loop

/--
[kwGraphLoopExponent_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalCancellation.lean)
-/
@[path]
private lemma kwGraphLoopExponent_surgery_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {selected : G.Dart}
  {loop : Fin n → G.Dart}
-- given
  (hboth : (∃ i, loop i = selected) ∧ ∃ j, loop j = selected.symm) :
-- imply
  kwGraphLoopExponent G (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) = kwGraphLoopExponent G loop := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopExponent_surgery G selected loop hboth

/--
[kwGraphLoopScalar_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalCancellation.lean)
-/
@[path]
private lemma kwGraphLoopScalar_surgery_sign_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {phase : G.Dart → G.Dart → ℂ}
  {selected : G.Dart}
  {loop : Fin n → G.Dart}
-- given
  (hpathSq : ∀ {N : ℕ} (path : Fin (N + 1) → G.Dart), path (Fin.last N) = (path 0).symm → (∀ j : Fin N, G.DartAdj (path j.castSucc) (path j.succ) ∧ (path j.castSucc).edge ≠ (path j.succ).edge) → (∏ j : Fin N, phase (path j.castSucc) (path j.succ)) ^ 2 = -1)
  (hphase : ∀ dart next, G.DartAdj dart next → dart.edge ≠ next.edge → phase next.symm dart.symm = (phase dart next)⁻¹)
  (hboth : (∃ i, loop i = selected) ∧ ∃ j, loop j = selected.symm) :
-- imply
  kwGraphLoopScalar G phase (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) = -kwGraphLoopScalar G phase loop := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopScalar_surgery_sign G phase hpathSq hphase selected loop hboth

/--
[kwGraphLoopWeight_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalCancellation.lean)
-/
@[path]
private lemma kwGraphLoopWeight_surgery_sign_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {weight : Sym2 V → ℂ}
  {phase : G.Dart → G.Dart → ℂ}
  {selected : G.Dart}
  {loop : Fin n → G.Dart}
-- given
  (hpathSq : ∀ {N : ℕ} (path : Fin (N + 1) → G.Dart), path (Fin.last N) = (path 0).symm → (∀ j : Fin N, G.DartAdj (path j.castSucc) (path j.succ) ∧ (path j.castSucc).edge ≠ (path j.succ).edge) → (∏ j : Fin N, phase (path j.castSucc) (path j.succ)) ^ 2 = -1)
  (hphase : ∀ dart next, G.DartAdj dart next → dart.edge ≠ next.edge → phase next.symm dart.symm = (phase dart next)⁻¹)
  (hboth : (∃ i, loop i = selected) ∧ ∃ j, loop j = selected.symm) :
-- imply
  StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight phase) (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) = -StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight phase) loop := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopWeight_surgery_sign G weight phase hpathSq hphase selected loop hboth

/--
[kwGraphLoopScalar_principal_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalCancellation.lean)
-/
@[path]
private lemma kwGraphLoopScalar_principal_surgery_sign_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {angle : G.Dart → Real.Angle}
  {selected : G.Dart}
  {loop : Fin n → G.Dart}
-- given
  (hangle : ∀ dart, angle dart.symm = angle dart + (Real.pi : Real.Angle))
  (hnonantipodal : ∀ dart next, G.DartAdj dart next → dart.edge ≠ next.edge → angle next - angle dart ≠ (Real.pi : Real.Angle))
  (hboth : (∃ i, loop i = selected) ∧ ∃ j, loop j = selected.symm) :
-- imply
  kwGraphLoopScalar G (kwPrincipalHalfAnglePhase angle) (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) = -kwGraphLoopScalar G (kwPrincipalHalfAnglePhase angle) loop := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopScalar_principal_surgery_sign G angle hangle hnonantipodal selected loop hboth

/--
[kwGraphLoopWeight_principal_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalCancellation.lean)
-/
@[path]
private lemma kwGraphLoopWeight_principal_surgery_sign_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {weight : Sym2 V → ℂ}
  {angle : G.Dart → Real.Angle}
  {selected : G.Dart}
  {loop : Fin n → G.Dart}
-- given
  (hangle : ∀ dart, angle dart.symm = angle dart + (Real.pi : Real.Angle))
  (hnonantipodal : ∀ dart next, G.DartAdj dart next → dart.edge ≠ next.edge → angle next - angle dart ≠ (Real.pi : Real.Angle))
  (hboth : (∃ i, loop i = selected) ∧ ∃ j, loop j = selected.symm) :
-- imply
  StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle)) (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) = -StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle)) loop := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopWeight_principal_surgery_sign G weight angle hangle hnonantipodal selected loop hboth

/--
[kw_principalAngleGraph_fixedOrbitExponent_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPrincipalCancellation.lean)
-/
@[path]
private lemma kw_principalAngleGraph_fixedOrbitExponent_cancel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {weight : Sym2 V → ℂ}
  {angle : G.Dart → Real.Angle}
  {selected : G.Dart}
  {exponent : Sym2 G.Dart →₀ ℕ}
-- given
  (hangle : ∀ dart, angle dart.symm = angle dart + (Real.pi : Real.Angle))
  (hnonantipodal : ∀ dart next, G.DartAdj dart next → dart.edge ≠ next.edge → angle next - angle dart ≠ (Real.pi : Real.Angle)) :
-- imply
  (∑ loop ∈ kwFixedOrbitExponentLoops (n := n) selected SimpleGraph.Dart.symm exponent, StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle)) loop) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_principalAngleGraph_fixedOrbitExponent_cancel G weight angle hangle hnonantipodal selected exponent


-- created on 2026-10-23
