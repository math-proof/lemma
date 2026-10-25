import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitSpinor.Part3
open StatMech StatMech.FrontierA


/--
[kwAngularSplitSpinorGauge_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean)
-/
@[path]
private lemma kwAngularSplitSpinorGauge_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d : (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart} :
-- imply
  kwAngularSplitSpinorGauge embedding d ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitSpinorGauge_ne_zero embedding d

/--
[kwPortAngleRoot_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean)
-/
@[path]
private lemma kwPortAngleRoot_sq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {p : KWDartPort G} :
-- imply
  kwPortAngleRoot embedding p ^ 2 = Complex.exp ((((embedding.dartAngle (kwDartOfPort G p)).toReal : Real) : Complex) * Complex.I) := by
-- proof
  apply StatMech.FrontierA.kwPortAngleRoot_sq embedding p

/--
[kwPortAngleRoot_sq_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean)
-/
@[path]
private lemma kwPortAngleRoot_sq_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d : G.Dart} :
-- imply
  kwPortAngleRoot embedding (kwPortOfDart G d.symm) ^ 2 = -(kwPortAngleRoot embedding (kwPortOfDart G d) ^ 2) := by
-- proof
  apply StatMech.FrontierA.kwPortAngleRoot_sq_symm embedding d

/--
[kwPortAngleRoot_sq_of_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean)
-/
@[path]
private lemma kwPortAngleRoot_sq_of_matching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {p q : KWDartPort G}
-- given
  (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm) :
-- imply
  kwPortAngleRoot embedding q ^ 2 = -(kwPortAngleRoot embedding p ^ 2) := by
-- proof
  apply StatMech.FrontierA.kwPortAngleRoot_sq_of_matching embedding hmatching

/--
[kwAngularSplitSpinorDirection_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean)
-/
@[path]
private lemma kwAngularSplitSpinorDirection_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d : (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart} :
-- imply
  kwAngularSplitSpinorDirection embedding d.symm = -kwAngularSplitSpinorDirection embedding d := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitSpinorDirection_symm embedding d

/--
[kwAngularSplitSpinorDirection_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean)
-/
@[path]
private lemma kwAngularSplitSpinorDirection_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d : (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart} :
-- imply
  kwAngularSplitSpinorDirection embedding d ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitSpinorDirection_ne_zero embedding d

/--
[kwAngularSplitSpinorPhase_sq_mul_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean)
-/
@[path]
private lemma kwAngularSplitSpinorPhase_sq_mul_direction_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d e : (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart}
-- given
  (hconnect : d.snd = e.fst)
  (hne : d.edge ≠ e.edge) :
-- imply
  kwAngularSplitSpinorPhase embedding d e ^ 2 * kwAngularSplitSpinorDirection embedding d = kwAngularSplitSpinorDirection embedding e := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitSpinorPhase_sq_mul_direction embedding d e hconnect hne

/--
[kwAngularSplitSpinorPath_sq_mul_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean)
-/
@[path]
private lemma kwAngularSplitSpinorPath_sq_mul_direction_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {N : Nat}
  {path : Fin (N + 1) → (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart}
-- given
  (hvalid : ∀ j : Fin N, (path j.castSucc).snd = (path j.succ).fst ∧ (path j.castSucc).edge ≠ (path j.succ).edge) :
-- imply
  (∏ j : Fin N, kwAngularSplitSpinorPhase embedding (path j.castSucc) (path j.succ)) ^ 2 * kwAngularSplitSpinorDirection embedding (path 0) = kwAngularSplitSpinorDirection embedding (path (Fin.last N)) := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitSpinorPath_sq_mul_direction embedding path hvalid

/--
[kwAngularSplitSpinorPath_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean)
-/
@[path]
private lemma kwAngularSplitSpinorPath_sq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {N : Nat}
  {path : Fin (N + 1) → (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart}
-- given
  (hend : path (Fin.last N) = (path 0).symm)
  (hvalid : ∀ j : Fin N, (path j.castSucc).snd = (path j.succ).fst ∧ (path j.castSucc).edge ≠ (path j.succ).edge) :
-- imply
  (∏ j : Fin N, kwAngularSplitSpinorPhase embedding (path j.castSucc) (path j.succ)) ^ 2 = -1 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitSpinorPath_sq embedding path hend hvalid

/--
[kwAngularSplitSpinorPhase_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean)
-/
@[path]
private lemma kwAngularSplitSpinorPhase_reverse_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d e : (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart}
-- given
  (hconnect : d.snd = e.fst)
  (hne : d.edge ≠ e.edge) :
-- imply
  kwAngularSplitSpinorPhase embedding e.symm d.symm = (kwAngularSplitSpinorPhase embedding d e)⁻¹ := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitSpinorPhase_reverse embedding d e hconnect hne

/--
[kwAngularSplitSpinorLoop_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean)
-/
@[path]
private lemma kwAngularSplitSpinorLoop_sq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : Nat}
  [NeZero n]
  {loop : Fin n → (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart}
-- given
  (hvalid : ∀ k : Fin n, (loop k).snd = (loop (k + 1)).fst ∧ (loop k).edge ≠ (loop (k + 1)).edge) :
-- imply
  (∏ k : Fin n, kwAngularSplitSpinorPhase embedding (loop k) (loop (k + 1))) ^ 2 = 1 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitSpinorLoop_sq embedding loop hvalid

/--
[kwAngularSplitGraphLoopWeight_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean)
-/
@[path]
private lemma kwAngularSplitGraphLoopWeight_surgery_sign_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : Nat}
  [NeZero n]
  {weight : Sym2 (KWDartPort G) → Complex}
  {selected : (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart}
  {loop : Fin n → (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart}
-- given
  (hboth : (∃ i, loop i = selected) ∧ ∃ j, loop j = selected.symm) :
-- imply
  StatMech.Onsager.ons_loopWeight (kwGraphTransition (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) weight (kwAngularSplitSpinorPhase embedding)) (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) = -StatMech.Onsager.ons_loopWeight (kwGraphTransition (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) weight (kwAngularSplitSpinorPhase embedding)) loop := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitGraphLoopWeight_surgery_sign embedding weight selected loop hboth

/--
[kwAngularSplitSpinor_formalRoot_coeff_eq_zero_of_repeated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean)
-/
@[path]
private lemma kwAngularSplitSpinor_formalRoot_coeff_eq_zero_of_repeated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {selected : (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart}
  {m : Sym2 (KWDartPort G) →₀ Nat}
-- given
  (hrepeated : 2 ≤ m selected.edge) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwAngularSplitSpinorPhase embedding)) = 0 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitSpinor_formalRoot_coeff_eq_zero_of_repeated embedding selected m hrepeated

/--
[kwAngularSplit_formalRoot_coeff_eq_zero_of_repeated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean)
-/
@[path]
private lemma kwAngularSplit_formalRoot_coeff_eq_zero_of_repeated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {selected : (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart}
  {m : Sym2 (KWDartPort G) →₀ Nat}
-- given
  (hrepeated : 2 ≤ m selected.edge) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwAngularSplitPhase embedding)) = 0 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_formalRoot_coeff_eq_zero_of_repeated embedding selected m hrepeated

/--
[kwAngularSplit_formalRoot_coeff_eq_zero_of_not_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean)
-/
@[path]
private lemma kwAngularSplit_formalRoot_coeff_eq_zero_of_not_squarefree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {m : Sym2 (KWDartPort G) →₀ Nat}
-- given
  (hm : ¬StatMech.Onsager.ons_IsSquarefreeExponent m) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwAngularSplitPhase embedding)) = 0 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_formalRoot_coeff_eq_zero_of_not_squarefree embedding m hm

/--
[kacWard_original_of_angularSplit_unitCycleLog_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean)
-/
@[path]
private lemma kacWard_original_of_angularSplit_unitCycleLog_closed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → Complex}
-- given
  (hunit : KWGraphUnitCycleLog (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwAngularSplitPhase embedding)) :
-- imply
  (1 - kwGraphTransition G weight embedding.turnPhase).det = (kwEvenPolynomial G weight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_original_of_angularSplit_unitCycleLog_closed embedding weight hunit


-- created on 2026-10-23
