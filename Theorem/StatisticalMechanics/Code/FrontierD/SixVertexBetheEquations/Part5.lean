/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part12
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part5
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexRootSymmetric.reverse_neg {n : ℕ} {p : Fin n → ℝ}
    (hp : SixVertexRootSymmetric p) :
    (fun j => -p j.rev) = p := by
  funext j
  rw [hp]
  simp

theorem sum_sixVertexTheta_pi_of_symmetric (c : ℝ)
    {n : ℕ} {p : Fin n → ℝ} (hp : SixVertexRootSymmetric p) :
    ∑ k, sixVertexTheta c Real.pi (p k) = -(n : ℝ) * Real.pi := by
  let S := ∑ k, sixVertexTheta c Real.pi (p k)
  have hrev : (∑ k : Fin n, sixVertexTheta c Real.pi (p k.rev)) = S := by
    apply Fintype.sum_equiv Fin.revPerm
    intro k
    rfl
  have hpair :
      S + S = ∑ k, (sixVertexTheta c Real.pi (p k) +
        sixVertexTheta c Real.pi (-p k)) := by
    calc
      S + S = S + ∑ k : Fin n, sixVertexTheta c Real.pi (p k.rev) := by rw [hrev]
      _ = S + ∑ k : Fin n, sixVertexTheta c Real.pi (-p k) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [hp]
      _ = _ := Finset.sum_add_distrib.symm
  have heval :
      (∑ k : Fin n, (sixVertexTheta c Real.pi (p k) +
        sixVertexTheta c Real.pi (-p k))) = -(2 * n : ℝ) * Real.pi := by
    simp_rw [sixVertexTheta_pi_pair]
    simp
    ring
  rw [heval] at hpair
  dsimp [S] at hpair ⊢
  linarith

theorem sum_sixVertexTheta_neg_pi_of_symmetric (c : ℝ)
    {n : ℕ} {p : Fin n → ℝ} (hp : SixVertexRootSymmetric p) :
    ∑ k, sixVertexTheta c (-Real.pi) (p k) = (n : ℝ) * Real.pi := by
  let S := ∑ k, sixVertexTheta c (-Real.pi) (p k)
  have hrev : (∑ k : Fin n, sixVertexTheta c (-Real.pi) (p k.rev)) = S := by
    apply Fintype.sum_equiv Fin.revPerm
    intro k
    rfl
  have hpair :
      S + S = ∑ k, (sixVertexTheta c (-Real.pi) (p k) +
        sixVertexTheta c (-Real.pi) (-p k)) := by
    calc
      S + S = S + ∑ k : Fin n, sixVertexTheta c (-Real.pi) (p k.rev) := by rw [hrev]
      _ = S + ∑ k : Fin n, sixVertexTheta c (-Real.pi) (-p k) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [hp]
      _ = _ := Finset.sum_add_distrib.symm
  have heval :
      (∑ k : Fin n, (sixVertexTheta c (-Real.pi) (p k) +
        sixVertexTheta c (-Real.pi) (-p k))) = (2 * n : ℝ) * Real.pi := by
    simp_rw [sixVertexTheta_neg_pi_pair]
    simp
    ring
  rw [heval] at hpair
  dsimp [S] at hpair ⊢
  linarith

theorem sixVertexBetheUpdate_eq_self_iff
    {c : ℝ} {N n : ℕ} (hN : 0 < N) (p : Fin n → ℝ) :
    sixVertexBetheUpdate c N n p = p ↔
      SixVertexSatisfiesBetheEquations c N n p := by
  constructor
  · intro h j
    have hj := congrFun h j
    unfold sixVertexBetheUpdate at hj
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp [hN0] at hj
    linarith
  · intro hp
    funext j
    unfold sixVertexBetheUpdate
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp [hN0]
    linarith [hp j]

theorem continuous_sixVertexBetheUpdate {c : ℝ} (hc : 2 < c)
    (N n : ℕ) :
    Continuous fun p : Fin n → ℝ => sixVertexBetheUpdate c N n p := by
  apply continuous_pi
  intro j
  unfold sixVertexBetheUpdate
  apply Continuous.div_const
  apply Continuous.sub continuous_const
  change Continuous fun p : Fin n → ℝ =>
    ∑ k ∈ Finset.univ, sixVertexTheta c (p j) (p k)
  apply continuous_finsetSum
  intro k _
  have hj : Continuous fun p : Fin n → ℝ => p j := continuous_apply j
  have hk : Continuous fun p : Fin n → ℝ => p k := continuous_apply k
  exact (continuous_sixVertexTheta hc).comp (hj.prodMk hk)

theorem sixVertexBetheUpdate_reverse_neg
    (c : ℝ) {N n : ℕ} (p : Fin n → ℝ) (j : Fin n) :
    sixVertexBetheUpdate c N n (fun k => -p k.rev) j =
      -sixVertexBetheUpdate c N n p j.rev := by
  have hsum :
      (∑ k : Fin n, sixVertexTheta c (p j.rev) (p k.rev)) =
        ∑ k : Fin n, sixVertexTheta c (p j.rev) (p k) := by
    apply Fintype.sum_equiv Fin.revPerm
    intro k
    rfl
  unfold sixVertexBetheUpdate
  rw [sixVertexCentralQuantumNumber_rev]
  simp only [sixVertexTheta_neg, Finset.sum_neg_distrib, hsum]
  ring

theorem sixVertexBetheUpdate_symmetric
    (c : ℝ) {N n : ℕ} {p : Fin n → ℝ}
    (hp : SixVertexRootSymmetric p) :
    SixVertexRootSymmetric (sixVertexBetheUpdate c N n p) := by
  intro j
  have hrev := sixVertexBetheUpdate_reverse_neg c (N := N) p j
  rw [hp.reverse_neg] at hrev
  linarith


end
end StatMech.FrontierD
