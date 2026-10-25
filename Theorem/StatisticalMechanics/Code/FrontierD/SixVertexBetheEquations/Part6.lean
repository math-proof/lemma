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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part6
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheUpdate_mem_openInterval {c : ℝ} (hc : 2 < c)
    {N n : ℕ} (hhalf : 2 * n ≤ N) {p : Fin n → ℝ}
    (hsymm : SixVertexRootSymmetric p)
    (hinterval : SixVertexRootsInOpenInterval p) :
    SixVertexRootsInOpenInterval (sixVertexBetheUpdate c N n p) := by
  intro j
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hN : 0 < N := lt_of_lt_of_le (by omega : 0 < 2 * n) hhalf
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hsumPi := sum_sixVertexTheta_pi_of_symmetric c hsymm
  have hsumNegPi := sum_sixVertexTheta_neg_pi_of_symmetric c hsymm
  have hsumUpper :
      (∑ k, sixVertexTheta c Real.pi (p k)) <
        ∑ k, sixVertexTheta c (p j) (p k) := by
    apply Finset.sum_lt_sum
    · intro k _
      exact (strictAnti_sixVertexTheta_left hc (p k) (hinterval j).2).le
    · exact ⟨j, Finset.mem_univ _,
        strictAnti_sixVertexTheta_left hc (p j) (hinterval j).2⟩
  have hsumLower :
      (∑ k, sixVertexTheta c (p j) (p k)) <
        ∑ k, sixVertexTheta c (-Real.pi) (p k) := by
    apply Finset.sum_lt_sum
    · intro k _
      exact (strictAnti_sixVertexTheta_left hc (p k) (hinterval j).1).le
    · exact ⟨j, Finset.mem_univ _,
        strictAnti_sixVertexTheta_left hc (p j) (hinterval j).1⟩
  have hjupper : (j.val : ℝ) ≤ (n : ℝ) - 1 := by
    have hjlt : (j.val : ℝ) < n := by exact_mod_cast j.isLt
    have hjint : (j.val : ℤ) < n := by exact_mod_cast j.isLt
    have hjstep : (j.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hjint
    linarith
  have hjlower : (0 : ℝ) ≤ j.val := by positivity
  have hIupper : sixVertexCentralQuantumNumber j ≤ ((n : ℝ) - 1) / 2 := by
    rw [sixVertexCentralQuantumNumber_eq]
    linarith
  have hIlower : -((n : ℝ) - 1) / 2 ≤ sixVertexCentralQuantumNumber j := by
    rw [sixVertexCentralQuantumNumber_eq]
    linarith
  have hhalfre : (2 : ℝ) * (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hhalf
  have hnre : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcount : (2 : ℝ) * (n : ℝ) - 1 < (N : ℝ) := by linarith
  unfold sixVertexBetheUpdate
  constructor
  · apply (lt_div_iff₀ hNreal).mpr
    rw [hsumNegPi] at hsumLower
    nlinarith [Real.pi_pos]
  · apply (div_lt_iff₀ hNreal).mpr
    rw [hsumPi] at hsumUpper
    nlinarith [Real.pi_pos]


theorem sixVertexBetheUpdate_strictMono {c : ℝ} (hc : 2 < c)
    {N n : ℕ} (hN : 0 < N) {p : Fin n → ℝ} (hp : StrictMono p) :
    StrictMono (sixVertexBetheUpdate c N n p) := by
  intro j k hjk
  have hpjk : p j < p k := hp hjk
  have htheta :
      (∑ l, sixVertexTheta c (p k) (p l)) <
        ∑ l, sixVertexTheta c (p j) (p l) := by
    apply Finset.sum_lt_sum
    · intro l _
      exact (strictAnti_sixVertexTheta_left hc (p l) hpjk).le
    · exact ⟨j, Finset.mem_univ _,
        strictAnti_sixVertexTheta_left hc (p j) hpjk⟩
  have hquantum := strictMono_sixVertexCentralQuantumNumber n hjk
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  unfold sixVertexBetheUpdate
  apply div_lt_div_of_pos_right _ hNreal
  nlinarith [Real.pi_pos]

theorem sixVertexBetheUpdate_strictMono_of_monotone {c : ℝ} (hc : 2 < c)
    {N n : ℕ} (hN : 0 < N) {p : Fin n → ℝ} (hp : Monotone p) :
    StrictMono (sixVertexBetheUpdate c N n p) := by
  intro j k hjk
  have hpjk : p j ≤ p k := hp hjk.le
  have htheta :
      (∑ l, sixVertexTheta c (p k) (p l)) ≤
        ∑ l, sixVertexTheta c (p j) (p l) := by
    apply Finset.sum_le_sum
    intro l _
    exact (strictAnti_sixVertexTheta_left hc (p l)).antitone hpjk
  have hquantum := strictMono_sixVertexCentralQuantumNumber n hjk
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  unfold sixVertexBetheUpdate
  apply div_lt_div_of_pos_right _ hNreal
  nlinarith [Real.pi_pos]


end
end StatMech.FrontierD
