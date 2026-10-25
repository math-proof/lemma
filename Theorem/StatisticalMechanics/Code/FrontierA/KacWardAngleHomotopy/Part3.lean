/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleGauge.Part4
import Mathlib.Topology.Connected.TotallyDisconnected
import Def.StatisticalMechanics.Code.FrontierA.KacWardAngleHomotopy.Part2
open scoped BigOperators
open Set SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager


theorem kwGraphTransition_one_eq_adjacency_mul_phase
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (dart next : G.Dart) :
    kwGraphTransition G (fun _ ↦ 1) phase dart next =
      (if dart.snd = next.fst ∧ dart.edge ≠ next.edge then 1 else 0) *
        phase dart next := by
  by_cases h : dart.snd = next.fst ∧ dart.edge ≠ next.edge
  · simp [kwGraphTransition, h]
  · simp [kwGraphTransition, h]


theorem kwGraphLoopScalar_eq_adjacency_mul_phaseProduct
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) :
    kwGraphLoopScalar G phase loop =
      kwGraphLoopAdjacency G loop * kwLoopPhaseProduct phase loop := by
  unfold kwGraphLoopScalar kwGraphLoopAdjacency kwLoopPhaseProduct
  rw [Finset.prod_congr rfl (fun k _ ↦
    kwGraphTransition_one_eq_adjacency_mul_phase
      G phase (loop k) (loop (k + 1))),
    Finset.prod_mul_distrib]

theorem kwGraphLoopAdjacency_eq_zero_of_not_nonbacktracking
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart)
    (hvalid : ¬kwGraphLoopNonbacktracking G loop) :
    kwGraphLoopAdjacency G loop = 0 := by
  classical
  simp only [kwGraphLoopNonbacktracking, not_forall] at hvalid
  obtain ⟨k, hk⟩ := hvalid
  unfold kwGraphLoopAdjacency
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp [hk]

theorem kwGraphLoopScalar_eq_of_valid_phaseProduct_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase₀ phase₁ : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart)
    (hphase : kwGraphLoopNonbacktracking G loop →
      kwLoopPhaseProduct phase₀ loop = kwLoopPhaseProduct phase₁ loop) :
    kwGraphLoopScalar G phase₀ loop = kwGraphLoopScalar G phase₁ loop := by
  rw [kwGraphLoopScalar_eq_adjacency_mul_phaseProduct,
    kwGraphLoopScalar_eq_adjacency_mul_phaseProduct]
  by_cases hvalid : kwGraphLoopNonbacktracking G loop
  · rw [hphase hvalid]
  · rw [kwGraphLoopAdjacency_eq_zero_of_not_nonbacktracking G loop hvalid,
      zero_mul, zero_mul]


theorem kwGraphFormalRoot_eq_of_valid_phaseProduct_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase₀ phase₁ : G.Dart → G.Dart → ℂ)
    (hphase : ∀ {n : ℕ} [NeZero n] (loop : Fin n → G.Dart),
      kwGraphLoopNonbacktracking G loop →
        kwLoopPhaseProduct phase₀ loop = kwLoopPhaseProduct phase₁ loop) :
    kwGraphFormalRoot G phase₀ = kwGraphFormalRoot G phase₁ := by
  have hlog : kwGraphFormalLog G phase₀ = kwGraphFormalLog G phase₁ := by
    ext m
    change kwGraphFormalLogCoeff G phase₀ m =
      kwGraphFormalLogCoeff G phase₁ m
    unfold kwGraphFormalLogCoeff
    apply congrArg (fun z : ℂ ↦ -z / 2)
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    apply Finset.sum_congr rfl
    intro loop _
    by_cases heq : kwGraphLoopExponent G loop = m
    · simp only [if_pos heq]
      exact kwGraphLoopScalar_eq_of_valid_phaseProduct_eq
        G phase₀ phase₁ loop (hphase loop)
    · simp [heq]
  unfold kwGraphFormalRoot
  rw [hlog]


theorem kwGraphFormalRoot_principalAngle_homotopy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (angle : ℝ → G.Dart → Real.Angle)
    (hcontinuous : ∀ dart next,
      dart.snd = next.fst ∧ dart.edge ≠ next.edge →
        ContinuousOn (fun t ↦ kwPrincipalHalfAnglePhase (angle t) dart next)
          (Icc 0 1)) :
    kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 1)) =
      kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 0)) := by
  symm
  apply kwGraphFormalRoot_eq_of_valid_phaseProduct_eq G
  intro n hn loop hvalid
  apply kwLoopPhaseProduct_principal_homotopy angle loop
  intro k
  exact hcontinuous (loop k) (loop (k + 1)) (hvalid k)


theorem kwGraphFormalRoot_principalAngle_nondegenerateHomotopy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (angle : ℝ → G.Dart → Real.Angle)
    (hangle : ∀ dart,
      ContinuousOn (fun t ↦ angle t dart) (Icc 0 1))
    (hnondegenerate : ∀ t ∈ Icc (0 : ℝ) 1, ∀ dart next,
      dart.snd = next.fst ∧ dart.edge ≠ next.edge →
        angle t next - angle t dart ≠ (Real.pi : Real.Angle)) :
    kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 1)) =
      kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 0)) := by
  apply kwGraphFormalRoot_principalAngle_homotopy G angle
  intro dart next hvalid
  exact kw_continuousOn_principalHalfAnglePhase angle (Icc 0 1)
    dart next (hangle dart) (hangle next)
      (fun t ht ↦ hnondegenerate t ht dart next hvalid)


theorem kw_detWalkRoot_principalAngle_homotopy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (angle : ℝ → G.Dart → Real.Angle)
    (hcontinuous : ∀ dart next,
      dart.snd = next.fst ∧ dart.edge ≠ next.edge →
        ContinuousOn (fun t ↦ kwPrincipalHalfAnglePhase (angle t) dart next)
          (Icc 0 1)) :
    ons_detWalkRoot (kwGraphTransition G weight
        (kwPrincipalHalfAnglePhase (angle 1))) =
      ons_detWalkRoot (kwGraphTransition G weight
        (kwPrincipalHalfAnglePhase (angle 0))) := by
  apply ons_detWalkRoot_eq_of_loopWeight_eq
  intro n loop
  rw [kwGraphLoopWeight_factor, kwGraphLoopWeight_factor]
  congr 1
  apply kwGraphLoopScalar_eq_of_valid_phaseProduct_eq
  intro hvalid
  symm
  apply kwLoopPhaseProduct_principal_homotopy angle loop
  intro k
  exact hcontinuous (loop k) (loop (k + 1)) (hvalid k)

theorem kw_detWalkRoot_principalAngle_nondegenerateHomotopy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (angle : ℝ → G.Dart → Real.Angle)
    (hangle : ∀ dart,
      ContinuousOn (fun t ↦ angle t dart) (Icc 0 1))
    (hnondegenerate : ∀ t ∈ Icc (0 : ℝ) 1, ∀ dart next,
      dart.snd = next.fst ∧ dart.edge ≠ next.edge →
        angle t next - angle t dart ≠ (Real.pi : Real.Angle)) :
    ons_detWalkRoot (kwGraphTransition G weight
        (kwPrincipalHalfAnglePhase (angle 1))) =
      ons_detWalkRoot (kwGraphTransition G weight
        (kwPrincipalHalfAnglePhase (angle 0))) := by
  apply kw_detWalkRoot_principalAngle_homotopy G weight angle
  intro dart next hvalid
  exact kw_continuousOn_principalHalfAnglePhase angle (Icc 0 1)
    dart next (hangle dart) (hangle next)
      (fun t ht ↦ hnondegenerate t ht dart next hvalid)


theorem kw_principalAngleHomotopy_formalRoot_coeff_eq_zero_of_repeated_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (direction : G.Dart → Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (gauge : G.Dart → ℂ) (hgauge : ∀ dart, gauge dart ≠ 0)
    (angle : ℝ → G.Dart → Real.Angle)
    (hstart : kwPrincipalHalfAnglePhase (angle 0) =
      kwPhaseGauge gauge (fun dart next ↦
        ons_turnW omega (direction next) (direction dart)))
    (hcontinuous : ∀ dart next,
      dart.snd = next.fst ∧ dart.edge ≠ next.edge →
        ContinuousOn (fun t ↦ kwPrincipalHalfAnglePhase (angle t) dart next)
          (Icc 0 1))
    (edge : Sym2 V) (hedge : edge ∈ G.edgeFinset)
    (m : Sym2 V →₀ ℕ) (hrepeated : 2 ≤ m edge) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 1))) = 0 := by
  rw [kwGraphFormalRoot_principalAngle_homotopy G angle hcontinuous,
    hstart]
  exact kw_rectilinearGraph_gaugedFormalRoot_coeff_eq_zero_of_repeated_edge
    G direction hdirection omega homega homega_sq gauge hgauge
      edge hedge m hrepeated


theorem kw_principalAngleNondegenerateHomotopy_formalRoot_coeff_eq_zero_of_repeated_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (direction : G.Dart → Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (gauge : G.Dart → ℂ) (hgauge : ∀ dart, gauge dart ≠ 0)
    (angle : ℝ → G.Dart → Real.Angle)
    (hstart : kwPrincipalHalfAnglePhase (angle 0) =
      kwPhaseGauge gauge (fun dart next ↦
        ons_turnW omega (direction next) (direction dart)))
    (hangle : ∀ dart,
      ContinuousOn (fun t ↦ angle t dart) (Icc 0 1))
    (hnondegenerate : ∀ t ∈ Icc (0 : ℝ) 1, ∀ dart next,
      dart.snd = next.fst ∧ dart.edge ≠ next.edge →
        angle t next - angle t dart ≠ (Real.pi : Real.Angle))
    (edge : Sym2 V) (hedge : edge ∈ G.edgeFinset)
    (m : Sym2 V →₀ ℕ) (hrepeated : 2 ≤ m edge) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 1))) = 0 := by
  rw [kwGraphFormalRoot_principalAngle_nondegenerateHomotopy
    G angle hangle hnondegenerate, hstart]
  exact kw_rectilinearGraph_gaugedFormalRoot_coeff_eq_zero_of_repeated_edge
    G direction hdirection omega homega homega_sq gauge hgauge
      edge hedge m hrepeated

end StatMech.FrontierA
