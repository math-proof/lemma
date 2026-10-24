import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAngleHomotopy
open Set SimpleGraph StatMech StatMech.FrontierA


/--
[kw_continuousAt_angleToReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kw_continuousAt_angleToReal_eq
  {θ : Real.Angle}
-- given
  (hθ : θ ≠ (Real.pi : Real.Angle)) :
-- imply
  ContinuousAt Real.Angle.toReal θ := by
-- proof
  apply StatMech.FrontierA.kw_continuousAt_angleToReal hθ

/--
[kw_continuousOn_principalHalfAnglePhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kw_continuousOn_principalHalfAnglePhase_eq
  [TopologicalSpace X]
  {angle : X → D → Real.Angle}
  {s : Set X}
  {dart next : D}
-- given
  (hdart : ContinuousOn (fun x ↦ angle x dart) s)
  (hnext : ContinuousOn (fun x ↦ angle x next) s)
  (hnondegenerate : ∀ x ∈ s, angle x next - angle x dart ≠ (Real.pi : Real.Angle)) :
-- imply
  ContinuousOn (fun x ↦ kwPrincipalHalfAnglePhase (angle x) dart next) s := by
-- proof
  apply StatMech.FrontierA.kw_continuousOn_principalHalfAnglePhase angle s dart next hdart hnext hnondegenerate

/--
[kwLoopPhaseProduct_branchHalfAngle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kwLoopPhaseProduct_branchHalfAngle_eq
  {n : ℕ}
  [NeZero n]
  {root : D → ℂ}
  {branch : D → D → ℂ}
  {loop : Fin n → D}
-- given
  (hroot : ∀ dart, root dart ≠ 0) :
-- imply
  kwLoopPhaseProduct (kwBranchHalfAnglePhase root branch) loop = kwLoopPhaseProduct branch loop := by
-- proof
  apply StatMech.FrontierA.kwLoopPhaseProduct_branchHalfAngle root branch hroot loop

/--
[kwLoopPhaseProduct_principal_eq_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kwLoopPhaseProduct_principal_eq_branch_eq
  {n : ℕ}
  [NeZero n]
  {angle : D → Real.Angle}
  {loop : Fin n → D} :
-- imply
  kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle) loop = kwLoopPhaseProduct (kwPrincipalHalfAngleBranch angle) loop := by
-- proof
  apply StatMech.FrontierA.kwLoopPhaseProduct_principal_eq_branch angle loop

/--
[kwLoopPhaseProduct_principal_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kwLoopPhaseProduct_principal_sq_eq
  {n : ℕ}
  [NeZero n]
  {angle : D → Real.Angle}
  {loop : Fin n → D} :
-- imply
  kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle) loop ^ 2 = 1 := by
-- proof
  apply StatMech.FrontierA.kwLoopPhaseProduct_principal_sq angle loop

/--
[kwLoopPhaseProduct_principal_eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kwLoopPhaseProduct_principal_eq_one_or_neg_one_eq
  {n : ℕ}
  [NeZero n]
  {angle : D → Real.Angle}
  {loop : Fin n → D} :
-- imply
  kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle) loop = 1 ∨ kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle) loop = -1 := by
-- proof
  apply StatMech.FrontierA.kwLoopPhaseProduct_principal_eq_one_or_neg_one angle loop

/--
[kwLoopPhaseProduct_eq_of_continuous_sign_homotopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kwLoopPhaseProduct_eq_of_continuous_sign_homotopy_eq
  {n : ℕ}
  [NeZero n]
  {phase : ℝ → D → D → ℂ}
  {loop : Fin n → D}
-- given
  (hcontinuous : ∀ k : Fin n, ContinuousOn (fun t ↦ phase t (loop k) (loop (k + 1))) (Icc 0 1))
  (hsign : ∀ t ∈ Icc (0 : ℝ) 1, kwLoopPhaseProduct (phase t) loop = 1 ∨ kwLoopPhaseProduct (phase t) loop = -1) :
-- imply
  kwLoopPhaseProduct (phase 0) loop = kwLoopPhaseProduct (phase 1) loop := by
-- proof
  apply StatMech.FrontierA.kwLoopPhaseProduct_eq_of_continuous_sign_homotopy phase loop hcontinuous hsign

/--
[kwLoopPhaseProduct_principal_homotopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kwLoopPhaseProduct_principal_homotopy_eq
  {n : ℕ}
  [NeZero n]
  {angle : ℝ → D → Real.Angle}
  {loop : Fin n → D}
-- given
  (hcontinuous : ∀ k : Fin n, ContinuousOn (fun t ↦ kwPrincipalHalfAnglePhase (angle t) (loop k) (loop (k + 1))) (Icc 0 1)) :
-- imply
  kwLoopPhaseProduct (kwPrincipalHalfAnglePhase (angle 0)) loop = kwLoopPhaseProduct (kwPrincipalHalfAnglePhase (angle 1)) loop := by
-- proof
  apply StatMech.FrontierA.kwLoopPhaseProduct_principal_homotopy angle loop hcontinuous

/--
[kwGraphTransition_one_eq_adjacency_mul_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kwGraphTransition_one_eq_adjacency_mul_phase_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {dart next : G.Dart} :
-- imply
  kwGraphTransition G (fun _ ↦ 1) phase dart next = (if dart.snd = next.fst ∧ dart.edge ≠ next.edge then 1 else 0) * phase dart next := by
-- proof
  apply StatMech.FrontierA.kwGraphTransition_one_eq_adjacency_mul_phase G phase dart next

/--
[kwGraphLoopScalar_eq_adjacency_mul_phaseProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kwGraphLoopScalar_eq_adjacency_mul_phaseProduct_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart} :
-- imply
  kwGraphLoopScalar G phase loop = kwGraphLoopAdjacency G loop * kwLoopPhaseProduct phase loop := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopScalar_eq_adjacency_mul_phaseProduct G phase loop

/--
[kwGraphLoopAdjacency_eq_zero_of_not_nonbacktracking](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kwGraphLoopAdjacency_eq_zero_of_not_nonbacktracking_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart}
-- given
  (hvalid : ¬kwGraphLoopNonbacktracking G loop) :
-- imply
  kwGraphLoopAdjacency G loop = 0 := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopAdjacency_eq_zero_of_not_nonbacktracking G loop hvalid

/--
[kwGraphLoopScalar_eq_of_valid_phaseProduct_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kwGraphLoopScalar_eq_of_valid_phaseProduct_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase₀ phase₁ : G.Dart → G.Dart → ℂ}
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart}
-- given
  (hphase : kwGraphLoopNonbacktracking G loop → kwLoopPhaseProduct phase₀ loop = kwLoopPhaseProduct phase₁ loop) :
-- imply
  kwGraphLoopScalar G phase₀ loop = kwGraphLoopScalar G phase₁ loop := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopScalar_eq_of_valid_phaseProduct_eq G phase₀ phase₁ loop hphase

/--
[kwGraphFormalRoot_eq_of_valid_phaseProduct_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kwGraphFormalRoot_eq_of_valid_phaseProduct_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase₀ phase₁ : G.Dart → G.Dart → ℂ}
-- given
  (hphase : ∀ {n : ℕ} [NeZero n] (loop : Fin n → G.Dart), kwGraphLoopNonbacktracking G loop → kwLoopPhaseProduct phase₀ loop = kwLoopPhaseProduct phase₁ loop) :
-- imply
  kwGraphFormalRoot G phase₀ = kwGraphFormalRoot G phase₁ := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_eq_of_valid_phaseProduct_eq G phase₀ phase₁ hphase

/--
[kwGraphFormalRoot_principalAngle_homotopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kwGraphFormalRoot_principalAngle_homotopy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {angle : ℝ → G.Dart → Real.Angle}
-- given
  (hcontinuous : ∀ dart next, dart.snd = next.fst ∧ dart.edge ≠ next.edge → ContinuousOn (fun t ↦ kwPrincipalHalfAnglePhase (angle t) dart next) (Icc 0 1)) :
-- imply
  kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 1)) = kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 0)) := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_principalAngle_homotopy G angle hcontinuous

/--
[kwGraphFormalRoot_principalAngle_nondegenerateHomotopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kwGraphFormalRoot_principalAngle_nondegenerateHomotopy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {angle : ℝ → G.Dart → Real.Angle}
-- given
  (hangle : ∀ dart, ContinuousOn (fun t ↦ angle t dart) (Icc 0 1))
  (hnondegenerate : ∀ t ∈ Icc (0 : ℝ) 1, ∀ dart next, dart.snd = next.fst ∧ dart.edge ≠ next.edge → angle t next - angle t dart ≠ (Real.pi : Real.Angle)) :
-- imply
  kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 1)) = kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 0)) := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_principalAngle_nondegenerateHomotopy G angle hangle hnondegenerate

/--
[kw_detWalkRoot_principalAngle_homotopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kw_detWalkRoot_principalAngle_homotopy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {weight : Sym2 V → ℂ}
  {angle : ℝ → G.Dart → Real.Angle}
-- given
  (hcontinuous : ∀ dart next, dart.snd = next.fst ∧ dart.edge ≠ next.edge → ContinuousOn (fun t ↦ kwPrincipalHalfAnglePhase (angle t) dart next) (Icc 0 1)) :
-- imply
  ons_detWalkRoot (kwGraphTransition G weight (kwPrincipalHalfAnglePhase (angle 1))) = ons_detWalkRoot (kwGraphTransition G weight (kwPrincipalHalfAnglePhase (angle 0))) := by
-- proof
  apply StatMech.FrontierA.kw_detWalkRoot_principalAngle_homotopy G weight angle hcontinuous

/--
[kw_detWalkRoot_principalAngle_nondegenerateHomotopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kw_detWalkRoot_principalAngle_nondegenerateHomotopy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {weight : Sym2 V → ℂ}
  {angle : ℝ → G.Dart → Real.Angle}
-- given
  (hangle : ∀ dart, ContinuousOn (fun t ↦ angle t dart) (Icc 0 1))
  (hnondegenerate : ∀ t ∈ Icc (0 : ℝ) 1, ∀ dart next, dart.snd = next.fst ∧ dart.edge ≠ next.edge → angle t next - angle t dart ≠ (Real.pi : Real.Angle)) :
-- imply
  ons_detWalkRoot (kwGraphTransition G weight (kwPrincipalHalfAnglePhase (angle 1))) = ons_detWalkRoot (kwGraphTransition G weight (kwPrincipalHalfAnglePhase (angle 0))) := by
-- proof
  apply StatMech.FrontierA.kw_detWalkRoot_principalAngle_nondegenerateHomotopy G weight angle hangle hnondegenerate

/--
[kw_principalAngleHomotopy_formalRoot_coeff_eq_zero_of_repeated_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kw_principalAngleHomotopy_formalRoot_coeff_eq_zero_of_repeated_edge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {direction : G.Dart → Fin 4}
  {omega : ℂ}
  {gauge : G.Dart → ℂ}
  {angle : ℝ → G.Dart → Real.Angle}
  {edge : Sym2 V}
  {m : Sym2 V →₀ ℕ}
-- given
  (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
  (homega : omega ≠ 0)
  (homega_sq : omega ^ 2 = Complex.I)
  (hgauge : ∀ dart, gauge dart ≠ 0)
  (hstart : kwPrincipalHalfAnglePhase (angle 0) = kwPhaseGauge gauge (fun dart next ↦ ons_turnW omega (direction next) (direction dart)))
  (hcontinuous : ∀ dart next, dart.snd = next.fst ∧ dart.edge ≠ next.edge → ContinuousOn (fun t ↦ kwPrincipalHalfAnglePhase (angle t) dart next) (Icc 0 1))
  (hedge : edge ∈ G.edgeFinset)
  (hrepeated : 2 ≤ m edge) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 1))) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_principalAngleHomotopy_formalRoot_coeff_eq_zero_of_repeated_edge G direction hdirection omega homega homega_sq gauge hgauge angle hstart hcontinuous edge hedge m hrepeated

/--
[kw_principalAngleNondegenerateHomotopy_formalRoot_coeff_eq_zero_of_repeated_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean)
-/
@[path]
private lemma kw_principalAngleNondegenerateHomotopy_formalRoot_coeff_eq_zero_of_repeated_edge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {direction : G.Dart → Fin 4}
  {omega : ℂ}
  {gauge : G.Dart → ℂ}
  {angle : ℝ → G.Dart → Real.Angle}
  {edge : Sym2 V}
  {m : Sym2 V →₀ ℕ}
-- given
  (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
  (homega : omega ≠ 0)
  (homega_sq : omega ^ 2 = Complex.I)
  (hgauge : ∀ dart, gauge dart ≠ 0)
  (hstart : kwPrincipalHalfAnglePhase (angle 0) = kwPhaseGauge gauge (fun dart next ↦ ons_turnW omega (direction next) (direction dart)))
  (hangle : ∀ dart, ContinuousOn (fun t ↦ angle t dart) (Icc 0 1))
  (hnondegenerate : ∀ t ∈ Icc (0 : ℝ) 1, ∀ dart next, dart.snd = next.fst ∧ dart.edge ≠ next.edge → angle t next - angle t dart ≠ (Real.pi : Real.Angle))
  (hedge : edge ∈ G.edgeFinset)
  (hrepeated : 2 ≤ m edge) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 1))) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_principalAngleNondegenerateHomotopy_formalRoot_coeff_eq_zero_of_repeated_edge G direction hdirection omega homega homega_sq gauge hgauge angle hstart hangle hnondegenerate edge hedge m hrepeated


-- created on 2026-10-23
