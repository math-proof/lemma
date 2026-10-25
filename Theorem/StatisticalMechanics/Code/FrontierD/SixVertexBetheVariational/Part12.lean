/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part7
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part12
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexChosenBetheSolution_mem_open
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (hhalf : 2 * n ≤ N) :
    SixVertexOpenRootSimplex (sixVertexChosenBetheSolution hc hhalf) :=
  (Classical.choose_spec (exists_sixVertexBetheSolution hc hhalf)).1

theorem sixVertexChosenBetheSolution_is_solution
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (hhalf : 2 * n ≤ N) :
    SixVertexSatisfiesBetheEquations c N n
      (sixVertexChosenBetheSolution hc hhalf) :=
  (Classical.choose_spec (exists_sixVertexBetheSolution hc hhalf)).2


theorem sixVertexBetheSolution_quantumSpacing
    {c : ℝ} (hc : 2 < c) {N n : ℕ} {p : Fin n → ℝ}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N n p)
    {i j : Fin n} (hij : i < j) :
    2 * Real.pi *
        (sixVertexCentralQuantumNumber j - sixVertexCentralQuantumNumber i) <
      (N : ℝ) * (p j - p i) := by
  have hpij : p i < p j := hopen.1 hij
  letI : Nonempty (Fin n) := ⟨i⟩
  have hsum :
      (∑ k, sixVertexTheta c (p j) (p k)) <
        ∑ k, sixVertexTheta c (p i) (p k) := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro k _
    exact strictAnti_sixVertexTheta_left hc (p k) hpij
  have hi := hsol i
  have hj := hsol j
  linarith


theorem sixVertexBetheSolution_adjacentSpacing
    {c : ℝ} (hc : 2 < c) {N n : ℕ} {p : Fin (n + 1) → ℝ}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (i : Fin n) :
    2 * Real.pi < (N : ℝ) * (p i.succ - p i.castSucc) := by
  have h := sixVertexBetheSolution_quantumSpacing hc hopen hsol
    (i := i.castSucc) (j := i.succ) (by simp)
  have hI : sixVertexCentralQuantumNumber i.succ -
      sixVertexCentralQuantumNumber i.castSucc = 1 := by
    rw [sixVertexCentralQuantumNumber_eq,
      sixVertexCentralQuantumNumber_eq]
    simp only [Fin.val_succ, Fin.val_castSucc]
    push_cast
    ring
  simpa [hI] using h

end
end StatMech.FrontierD
